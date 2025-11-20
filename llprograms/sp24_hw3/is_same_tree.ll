; is same tree leetcode problem
; sample Java code
; class Solution {
;     public boolean isSameTree(TreeNode p, TreeNode q) {
;         return dfs(p, q);
;     }

;     private boolean dfs(TreeNode p, TreeNode q) {
;         if (p == null && q == null) {
;             return true;
;         }

;         if (p == null || q == null) {
;             return false;
;         }

;         if (p.val != q.val) return false;

;         boolean left = dfs(p.left, q.left);
;         boolean right = dfs(p.right, q.right);

;         return left && right;
;     }
; }

; val, left child, right child
%TreeNode = type { %TreeNode*, %TreeNode*, i64 }

; test with root1 = [1,2,3], root2 = [1,2,3], type
@n2 = global %TreeNode { %TreeNode* null, %TreeNode* null, i64 2 }
@n3 = global %TreeNode { %TreeNode* null, %TreeNode* null, i64 3 }
@root1 = global %TreeNode { %TreeNode* @n2, %TreeNode* @n3, i64 1 }

@n2_2 = global %TreeNode { %TreeNode* null, %TreeNode* null, i64 2 }
@n3_2 = global %TreeNode { %TreeNode* null, %TreeNode* null, i64 3 }
@root2 = global %TreeNode { %TreeNode* @n2_2, %TreeNode* @n3_2, i64 1 }

; root1 = [1,2,3], root3 = [1,null,3] false, modify input & expected to test
@n3_3 = global %TreeNode { %TreeNode* null, %TreeNode* null, i64 3 }
@root3 = global %TreeNode { %TreeNode* null, %TreeNode* @n3_3, i64 1 }

define i1 @is_same_tree(%TreeNode* %r1, %TreeNode* %r2) {
entry:
    %r1_check = icmp eq %TreeNode* %r1, null 
    %r2_check = icmp eq %TreeNode* %r2, null 
    ; check both leaves
    %both_true = and i1 %r1_check, %r2_check
    %both_cond = icmp eq i1 1, %both_true
    br i1 %both_cond, label %ret_true, label %one_null
one_null: 
    %one_true = or i1 %r1_check, %r2_check
    %one_cond = icmp eq i1 1, %one_true
    br i1 %one_cond, label %ret_false, label %no_null
no_null: 
  ; compare value
  %val1_ptr= getelementptr %TreeNode, %TreeNode* %r1, i64 0, i32 2
  %val1 = load i64, i64* %val1_ptr

  %val2_ptr = getelementptr %TreeNode, %TreeNode* %r2, i64 0, i32 2
  %val2 = load i64, i64* %val2_ptr

  %same_val = icmp eq i64 %val1, %val2
  br i1 %same_val, label %equal_val, label %ret_false
equal_val:
  ; get both children from both roots
  %left1_p = getelementptr %TreeNode, %TreeNode* %r1, i64 0, i32 0
  %left1 = load %TreeNode*, %TreeNode** %left1_p
  %right1_p = getelementptr %TreeNode, %TreeNode* %r1, i64 0, i32 1
  %right1 = load %TreeNode*, %TreeNode** %right1_p

  %left2_p = getelementptr %TreeNode, %TreeNode* %r2, i64 0, i32 0
  %left2 = load %TreeNode*, %TreeNode** %left2_p
  %right2_p = getelementptr %TreeNode, %TreeNode* %r2, i64 0, i32 1
  %right2 = load %TreeNode*, %TreeNode** %right2_p

  ; left subtree dfs
  %left_sub = call i1 @is_same_tree(%TreeNode* %left1, %TreeNode* %left2)
  ; right subtree dfs
  %right_sub  = call i1 @is_same_tree(%TreeNode* %right1, %TreeNode* %right2)
  ; return left && right
  %subs_same = and i1 %left_sub, %right_sub
  br i1 %subs_same, label %ret_true, label %ret_false
ret_true:
  ret i1 1
ret_false:
  ret i1 0
}

define i1 @main(i64 %argc, i8** %argv) {
  %res = call i1 @is_same_tree(%TreeNode* @root1, %TreeNode* @root2)
  ret i1 %res
}