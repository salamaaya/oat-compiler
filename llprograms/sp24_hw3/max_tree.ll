; Finds the maximum value in a binary tree

%struct.Node = type { %struct.Node*, %struct.Node*, i64 }

@node1 = global %struct.Node { %struct.Node* null, %struct.Node* null, i64 100 }
@node2 = global %struct.Node { %struct.Node* @node1, %struct.Node* null, i64 10 }
@node3 = global %struct.Node { %struct.Node* null, %struct.Node* null, i64 1 }
@test1 = global %struct.Node { %struct.Node* @node2, %struct.Node* @node3, i64 5 }
@test2 = global %struct.Node { %struct.Node* @test1, %struct.Node* null, i64 1000 }
@test3 = global %struct.Node { %struct.Node* @test2, %struct.Node* null, i64 100 }

define i64 @find_max(%struct.Node* %node) {
entry:
  ; Check if node is null
  %is_null = icmp eq %struct.Node* %node, null
  br i1 %is_null, label %return_default, label %not_null

return_default:
  ; If node is null, return default value
  ret i64 0

not_null:
  ; If node is not null, continue with the rest of the function
  ; Initialize max to the value of the root node
  %value_ptr_root = getelementptr %struct.Node, %struct.Node* %node, i32 0, i32 2
  %root_value = load i64, i64* %value_ptr_root
  %max = alloca i64
  store i64 %root_value, i64* %max

  ; Initialize left and right maximum values to 0
  %left_max = alloca i64
  store i64 0, i64* %left_max
  %right_max = alloca i64
  store i64 0, i64* %right_max

  ; Start loop iteration
  br label %loop
  
loop:
  ; Load current node's value
  %value_ptr = getelementptr %struct.Node, %struct.Node* %node, i32 0, i32 2
  %value = load i64, i64* %value_ptr

  ; Load the current maximum value
  %old_max = load i64, i64* %max
  
  ; Compare current value with the maximum value
  %is_greater = icmp sgt i64 %value, %old_max
  
  ; If current value is greater, update maximum value
  br i1 %is_greater, label %update_max, label %check_left
  
update_max:
  ; Store the current value as the new maximum
  store i64 %value, i64* %max
  br label %check_left

check_left:
  ; Check if left child exists
  %left_child_ptr = getelementptr %struct.Node, %struct.Node* %node, i32 0, i32 0
  %left_child = load %struct.Node*, %struct.Node** %left_child_ptr
  %is_left_null = icmp eq %struct.Node* %left_child, null
  br i1 %is_left_null, label %check_right, label %visit_left
  
visit_left:
  ; Recurse on left child
  %left_max_value = call i64 @find_max(%struct.Node* %left_child)
  store i64 %left_max_value, i64* %left_max
  br label %check_right
  
check_right:
  ; Check if right child exists
  %right_child_ptr = getelementptr %struct.Node, %struct.Node* %node, i32 0, i32 1
  %right_child = load %struct.Node*, %struct.Node** %right_child_ptr
  %is_right_null = icmp eq %struct.Node* %right_child, null
  br i1 %is_right_null, label %end_loop, label %visit_right
  
visit_right:
  ; Recurse on right child
  %right_max_value = call i64 @find_max(%struct.Node* %right_child)
  store i64 %right_max_value, i64* %right_max
  br label %end_loop
  
end_loop:
  ; Get current maximum value from root
  %final_max = load i64, i64* %max
  ; Get the maximum value from left and right subtrees
  %final_left_max = load i64, i64* %left_max
  %final_right_max = load i64, i64* %right_max
  ; Compare maximum values from left and right subtrees
  %is_left_greater = icmp sgt i64 %final_left_max, %final_right_max
  br i1 %is_left_greater, label %left_greater, label %right_greater

left_greater:
  ; Check with middle
  %is_middle_greater_left = icmp sgt i64 %final_max, %final_left_max
  br i1 %is_middle_greater_left, label %return_middle_max, label %return_left_max

return_left_max:
  ; If left maximum is greater, return it
  ret i64 %final_left_max

right_greater:
  ; Check with middle
  %is_middle_greater_right = icmp sgt i64 %final_max, %final_right_max
  br i1 %is_middle_greater_right, label %return_middle_max, label %return_right_max
  
return_right_max:
  ; If right maximum is greater, return it
  ret i64 %final_right_max

return_middle_max:
  ; If middle maximum is greater, return it
  ret i64 %final_max
}

define i64 @main(i64 %argc, i8** %argv) {
  %res1 = call i64 @find_max(%struct.Node* @test1)
  %cmp1 = icmp eq i64 %res1, 100
  br i1 %cmp1, label %test2, label %FAIL
test2:
  %res2 = call i64 @find_max(%struct.Node* @test2)
  %cmp2 = icmp eq i64 %res2, 1000
  br i1 %cmp2, label %test3, label %FAIL
test3:
  %res3 = call i64 @find_max(%struct.Node* @test3)
  %cmp3 = icmp eq i64 %res3, 1000
  br i1 %cmp3, label %node1, label %FAIL
node1:
  %res4 = call i64 @find_max(%struct.Node* @node1)
  %cmp4 = icmp eq i64 %res4, 100
  br i1 %cmp4, label %node2, label %FAIL
node2:
  %res5 = call i64 @find_max(%struct.Node* @node2)
  %cmp5 = icmp eq i64 %res5, 100
  br i1 %cmp5, label %node3, label %FAIL
node3:
  %res6 = call i64 @find_max(%struct.Node* @node3)
  %cmp6 = icmp eq i64 %res6, 1
  br i1 %cmp6, label %PASS, label %FAIL
PASS: 
  ret i64 1
FAIL:
  ret i64 0
}
