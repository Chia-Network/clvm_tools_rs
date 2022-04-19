/*
 * We treat an s-expression as a binary tree, where leaf nodes are atoms and pairs
 * are nodes with two children. We then number the paths as follows:
 *               1
 *              / \
 *             /   \
 *            /     \
 *           /       \
 *          /         \
 *         /           \
 *        2             3
 *       / \           / \
 *      /   \         /   \
 *     4      6      5     7
 *    / \    / \    / \   / \
 *   8   12 10  14 9  13 11  15
 * etc.
 * You're probably thinking "the first two rows make sense, but why do the numbers
 * do that weird thing after?" The reason has to do with making the implementation simple.
 * We want a simple loop which starts with the root node, then processes bits starting with
 * the least significant, moving either left or right (first or rest). So the LEAST significant
 * bit controls the first branch, then the next-least the second, and so on. That leads to this
 * ugly-numbered tree.
 */

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero, Bytes};
use crate::classic::clvm::casts::{bigint_from_bytes, bigint_to_bytes, TConvertOption};
use crate::util::Number;

pub fn compose_paths(path_0_: &Number, path_1_: &Number) -> Number {
    let path_0 = path_0_.clone();
    let mut path_1 = path_1_.clone();

    /*
     * The binary representation of a path is a 1 (which means "stop"), followed by the
     * path as binary digits, where 0 is "left" and 1 is "right".
     * Look at the diagram at the top for these examples.
     * Example: 9 = 0b1001, so right, left, left
     * Example: 10 = 0b1010, so left, right, left
     * How it works: we write both numbers as binary. We ignore the terminal in path_0, since it's
     * not the terminating condition anymore. We shift path_1 enough places to OR in the rest of path_0.
     * Example: path_0 = 9 = 0b1001, path_1 = 10 = 0b1010.
     * Shift path_1 three places (so there is room for 0b001) to 0b1010000.
     * Then OR in 0b001 to yield 0b1010001 = 81, which is right, left, left, left, right, left.
     */
    let mut mask = bi_one();
    let mut temp_path = path_0.clone();
    while temp_path > bi_one() {
        path_1 <<= 1;
        mask <<= 1;
        temp_path >>= 1;
    }

    mask -= bi_one();
    path_1 | (path_0 & mask)
}

pub struct NodePath {
    /*
     * Use 1-based paths
     */
    index: Number,
}

impl NodePath {
    pub fn new(index: Option<Number>) -> Self {
        match index {
            Some(index) => {
                if index < bi_zero() {
                    let bytes_repr =
                        bigint_to_bytes(&index, Some(TConvertOption { signed: true })).unwrap();
                    let unsigned = bigint_from_bytes(&bytes_repr, None);
                    NodePath { index: unsigned }
                } else {
                    NodePath {
                        index: index.clone(),
                    }
                }
            }
            None => NodePath { index: bi_one() },
        }
    }

    pub fn as_path(&self) -> Bytes {
        bigint_to_bytes(&self.index, None).unwrap()
    }

    pub fn add(&self, other_node: NodePath) -> Self {
        let composedPath = compose_paths(&self.index, &other_node.index);
        NodePath::new(Some(composedPath))
    }

    pub fn first(&self) -> Self {
        NodePath::new(Some(self.index.clone() * 2_u32.to_bigint().unwrap()))
    }

    pub fn rest(&self) -> Self {
        NodePath::new(Some(
            (self.index.clone() * 2_u32.to_bigint().unwrap()) + bi_one(),
        ))
    }
}

//   public toString(){
//     return `NodePath: ${this.index}`;
//   }

//   public __repl__(){
//     return `NodePath: ${this.index}`;
//   }
// }
