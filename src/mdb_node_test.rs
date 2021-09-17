use super::*;

#[test]
fn test_node() {
    let entry = Entry::new(200, 1);
    let mut node: Node<u32, u32> = (10, entry).into();
    assert!(!node.is_black());
    assert!(node.as_left_ref().is_none());
    assert!(node.as_right_ref().is_none());
    assert_eq!(*node.as_key(), 10);
    assert_eq!(node.to_seqno(), 1);

    node.set_red();
    assert!(!node.is_black());
    node.set_black();
    assert!(node.is_black());
    node.toggle_link();
    assert!(!node.is_black());

    node.set(300, 2);
    assert!(Entry::new(300, 2) == node.entry.as_ref().clone());
}
