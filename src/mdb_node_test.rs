use super::*;

#[test]
fn test_node() {
    let entry = Entry::new(200, 1);
    let mut node: Node<u32, u32> = (10, entry).into();
    assert_eq!(node.is_black(), false);
    assert_eq!(node.as_left_ref().is_none(), true);
    assert_eq!(node.as_right_ref().is_none(), true);
    assert_eq!(*node.as_key(), 10);
    assert_eq!(node.to_seqno(), 1);

    node.set_red();
    assert_eq!(node.is_black(), false);
    node.set_black();
    assert_eq!(node.is_black(), true);
    node.toggle_link();
    assert_eq!(node.is_black(), false);

    node.set(300, 2);
    assert_eq!(Entry::new(300, 2), node.entry.as_ref().clone());
}
