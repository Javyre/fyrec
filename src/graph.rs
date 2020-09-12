use std::fmt::{Display, Debug};
use std::hash::Hash;

use bitflags::bitflags;
use indexmap::{IndexMap, IndexSet};

pub trait Id: Hash + Eq + Clone + Debug + Display { }
impl<T> Id for T where T: Hash + Eq + Clone + Debug + Display {}

pub trait IGraphNode<I: Id> : Debug {
    fn get_id(&self) -> I;
    fn get_deps<'a>(&self) -> IndexSet<&I>;
}

pub trait IGraphCtx<I: Id, N: IGraphNode<I>, E> {
    fn get_node(&self, id: &I) -> Result<&N, E>;
}

bitflags! {
    #[derive(Default)]
    struct NodeFlags: u8 {
        const VISITED      = 0b0001;
        const VISITING     = 0b0010;
        const GROUPED      = 0b0100;
        const SELF_GROUPED = 0b1000;
    }
}

#[derive(Debug)]
struct NodeInfo<'a, N> {
    // derive default to 0
    flags: NodeFlags,

    recurs: Option<Vec<&'a N>>,
}

impl<'a, N> Default for NodeInfo<'a, N> {
    fn default() -> Self {
        Self {
            flags: Default::default(),
            recurs: None,
        }
    }
}

struct Info<'a, I: Id, N: IGraphNode<I>>(
    IndexMap<I, NodeInfo<'a, N>>
);

impl<'a, I: Id, N: IGraphNode<I>> Info<'a, I, N> {
    fn with_capacity(c: usize) -> Self {
        Self(IndexMap::with_capacity(c))
    }

    fn has_flag(&self, id: &I, flag: NodeFlags) -> bool {
        self.0.get(id).map_or(false, |i| i.flags & flag == flag)
    }
    fn recurs(&self, id: &I) -> &Option<Vec<&'a N>> {
        self.0.get(id).map_or(&None, |i| &i.recurs)
    }

    fn set_flag(&mut self, id: &I, flag: NodeFlags) {
        if !self.0.contains_key(id) {
            let mut new: NodeInfo<'a, N> = Default::default();
            new.flags |= flag;
            self.0.insert(id.clone(), new);
        } else {
            self.0.get_mut(id).unwrap().flags |= flag;
        }
    }
    fn unset_flag(&mut self, id: &I, flag: NodeFlags) {
        if !self.0.contains_key(id) {
            let mut new: NodeInfo<'a, N> = Default::default();
            self.0.insert(id.clone(), new);
        } else {
            self.0.get_mut(id).unwrap().flags &= !flag;
        }
    }
    fn set_recurs(&mut self, id: &I, v: Option<Vec<&'a N>>) {
        if !self.0.contains_key(id) {
            let mut new: NodeInfo<'a, N> = Default::default();
            new.recurs = v;
            self.0.insert(id.clone(), new);
        } else {
            self.0.get_mut(id).unwrap().recurs = v;
        }
    }
    fn remove_recurs(&mut self, id: &I) -> Option<Vec<&'a N>> {
        if !self.0.contains_key(id) {
            None
        } else {
            let mut r = None;
            std::mem::swap(&mut self.0.get_mut(id).unwrap().recurs, &mut r);
            r
        }
    }
}


pub fn topological_sort<
    'a,
    I: Id,
    N: IGraphNode<I>,
    C: IGraphCtx<I, N, E>,
    E
>(
    ctx: &'a C,
    nodes: &Vec<&'a N>
) -> Result<Vec<Vec<&'a N>>, E> {

    let mut info  = Info::<'a, I, N>::with_capacity(nodes.len());
    let mut trace = Vec::<I>::with_capacity(nodes.len());
    let mut r = Vec::<Vec<&'a N>>::with_capacity(nodes.len());
    for node in nodes {
        let id = node.get_id();
        if info.has_flag(&id, NodeFlags::VISITED) {
            continue;
        }
        visit(*node, ctx, &mut info, &mut trace, &mut r)?;
    }
    Ok(r)
}

fn visit<
    'a,
    I: Id,
    N: IGraphNode<I>,
    C: IGraphCtx<I, N, E>,
    E,
>(
    node: &'a N,
    ctx: &'a C,
    info: &mut Info<'a, I, N>,
    trace: &mut Vec<I>,
    r: &mut Vec<Vec<&'a N>>
) -> Result<(), E> {
    let id = node.get_id();

    if info.has_flag(&id, NodeFlags::SELF_GROUPED) {
        // TODO: better error message so one can find out where the problem is
        // in their code
        
        // probably not ever actually a good idea to implement this
        todo!("two or more recursive groups sharing more than one node: {}", &id);
    }

    if info.has_flag(&id, NodeFlags::VISITED) {
        return Ok(());
    }

    if info.has_flag(&id, NodeFlags::VISITING) {
        // If we are already VISITING this node,
        // then the trace contains one of every nodeID in the recursive group

        let mut new_rec_group = Vec::with_capacity(trace.len());
        for prev in trace.iter().skip_while(|&i| *i != id) {
            if info.has_flag(prev, NodeFlags::GROUPED) {
                // probably not ever actually a good idea to implement this
                todo!("nodes simultaneously in multiple recursive groups");
            }

            info.set_flag(prev, NodeFlags::GROUPED);
            info.set_flag(prev, NodeFlags::SELF_GROUPED);
            new_rec_group.push(ctx.get_node(prev)?);

            if info.recurs(prev).is_none() {
                info.set_recurs(prev, Some(vec![]));
            }
        }

        info.set_recurs(&id, Some(new_rec_group));

        return Ok(());
    }

    info.set_flag(&id, NodeFlags::VISITING);
    trace.push(id.clone());
    for dependency in node.get_deps().iter() {
        let dependency = ctx.get_node(dependency)?;
        visit(dependency, ctx, info, trace, r)?;
    }
    trace.pop();
    info.unset_flag(&id, NodeFlags::VISITING);
    info.set_flag(&id, NodeFlags::VISITED);

    if let Some(rec) = info.remove_recurs(&id) {
        if rec.len() > 0 {
            for n in rec.iter() {
                info.unset_flag(&n.get_id(), NodeFlags::SELF_GROUPED);
            }
            r.push(rec);
        }
    } else {
        r.push(vec![node]);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use indexmap::IndexMap;

    struct Context(IndexMap<usize, Node>);

    impl Context {
        fn new(nodes: Vec<Node>) -> Self {
            let mut map = IndexMap::with_capacity(nodes.len());
            for n in nodes.into_iter() {
                map.insert(n.0, n);
            }
            Self(map)
        }

        // predictable order for test reproducibility
        fn get_nodes(&self) -> Vec<&Node> {
            // sort the nodes by id for consistency when testing
            // order of map.values() is undefined
            let mut nodes = self.0.values().collect::<Vec<&Node>>();
            nodes.sort_by_key(|n| n.get_id());

            nodes
        }
    }

    impl IGraphCtx<usize, Node, ()> for Context {
        fn get_node(&self, id: &usize) -> Result<&Node, ()> {
            Ok(self.0.get(id).unwrap())
        }
    }

    #[derive(Debug)]
    struct Node(usize, Vec<usize>);

    impl IGraphNode<usize> for Node {
        fn get_id(&self) -> usize {
            self.0
        }
        fn get_deps(&self) -> IndexSet<&usize> {
            self.1.iter().collect()
        }
    }

    fn assert_sorted(nodes: Vec<Node>, expect: Vec<Vec<usize>>) {
        let ctx = Context::new(nodes);

        let sorted = dbg!(topological_sort(&ctx, &ctx.get_nodes())).unwrap();
        assert_eq!(sorted.len(), expect.len());
        for (r, e) in sorted.iter().zip(expect.iter()) {
            assert_eq!(r.len(), e.len());
            for (&rr, &ee) in r.iter().zip(e.iter()) {
                assert_eq!(rr.0, ee);
            }
        }
    }

    #[test]
    fn simple() {
        let nodes = vec![
            Node(0, vec![1]),
            Node(1, vec![3]),
            Node(2, vec![0, 1]),
            Node(3, vec![]),
        ];

        let expected = vec![
            vec![3],
            vec![1],
            vec![0],
            vec![2],
        ];

        assert_sorted(nodes, expected);
    }

    #[test]
    fn one_group() {
        let nodes = vec![
            Node(0, vec![2]),
            Node(1, vec![0]),
            Node(2, vec![1]),
            Node(3, vec![1]),
        ];

        let expect = vec![
            vec![0, 2, 1],
            vec![3],
        ];

        assert_sorted(nodes, expect);
    }

    #[test]
    fn one_group_dependency() {
        let nodes = vec![
            Node(0, vec![1, 5]),
            Node(1, vec![0]),
            Node(2, vec![3]),
            Node(3, vec![1, 4]),
            Node(4, vec![0]),
            Node(5, vec![])
        ];

        let expected = vec![
            vec![5],
            vec![0, 1],
            vec![4],
            vec![3],
            vec![2],
        ];

        assert_sorted(nodes, expected);
    }

    // shared group dependency is unimplemented
    // (and impossible to order topoogically)
    #[test]
    #[should_panic]
    fn two_group_dependencies_unimpl() {
        let nodes = vec![
            Node(0, vec![1]),
            Node(1, vec![0, 2]),
            Node(2, vec![1]),
        ];

        let ctx = Context::new(nodes);
        dbg!(topological_sort(&ctx, &ctx.get_nodes())).unwrap();
    }

    #[test]
    #[should_panic]
    fn two_group_dependencies_unimpl2() {
        let nodes = vec![
            Node(0, vec![1]),
            Node(1, vec![0, 2]),
            Node(2, vec![3]),
            Node(3, vec![2, 1]),
        ];

        let ctx = Context::new(nodes);
        dbg!(topological_sort(&ctx, &ctx.get_nodes())).unwrap();
    }

    #[test]
    #[should_panic]
    fn two_group_dependencies_unimpl3() {
        let nodes = vec![
            // Node(0, vec![3, 4]),
            // Node(1, vec![4]),
            // Node(2, vec![0]),
            // Node(3, vec![0]),
            // Node(4, vec![3]),
            Node(0, vec![1, 2]),
            Node(1, vec![0]),
            Node(2, vec![1]),
        ];

        let ctx = Context::new(nodes);
        dbg!(topological_sort(&ctx, &ctx.get_nodes())).unwrap();
    }

    #[test]
    fn two_group_dependency() {
        let nodes = vec![
            Node(0, vec![1]),
            Node(1, vec![0, 2]),
            Node(2, vec![3]),
            Node(3, vec![2]),
        ];

        let expected = vec![
            vec![2, 3],
            vec![0, 1],
        ];

        assert_sorted(nodes, expected);
    }
}
