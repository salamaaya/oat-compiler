@test_case = global [8 x i64] [i64 10, i64 9, i64 2, i64 5, i64 3, i64 7, i64 101, i64 18]
@memo = global [8 x i64] [i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1, i64 -1]

define i64 @max_in_memo() {
  %max = alloca i64
  store i64 -1, i64* %max

  ; loop variable, we can skip index 0 because it's the base case
  %i = alloca i64
  store i64 0, i64* %i

  br label %loop

loop:
  %i_val = load i64, i64* %i
  %cmp1 = icmp eq i64 %i_val, 8

  br i1 %cmp1, label %after_loop, label %loop_body

loop_body:
  %memo_val_ptr = getelementptr [8 x i64], [8 x i64]* @memo, i32 0, i64 %i_val
  %memo_val = load i64, i64* %memo_val_ptr
  %max_val1 = load i64, i64* %max
  %cmp2 = icmp sgt i64 %memo_val, %max_val1

  br i1 %cmp2, label %new_max, label %repeat_loop

new_max:
  store i64 %memo_val, i64* %max

  br label %repeat_loop

repeat_loop:
  %new_i_val = add i64 %i_val, 1
  store i64 %new_i_val, i64* %i

  br label %loop

after_loop:
  %max_val2 = load i64, i64* %max

  ret i64 %max_val2
}

define i64 @lis(i64 %idx) {
  %max = alloca i64
  store i64 1, i64* %max

  ; loop variable
  %i = alloca i64
  store i64 0, i64* %i

  br label %loop

loop:
  %i_val = load i64, i64* %i
  %cmp1 = icmp eq i64 %i_val, %idx

  br i1 %cmp1, label %after_loop, label %loop_body 

loop_body:
  %memo_val_ptr = getelementptr [8 x i64], [8 x i64]* @memo, i32 0, i64 %i_val
  %memo_val1 = load i64, i64* %memo_val_ptr

  ; check if we've previously memoized the result for this subproblem
  %cmp2 = icmp eq i64 %memo_val1, -1
  
  br i1 %cmp2, label %recurse, label %after_memo

recurse:
  %res = call i64 @lis(i64 %i_val)
  store i64 %res, i64* %memo_val_ptr

  br label %after_memo

after_memo:
  %arr_i_ptr = getelementptr [8 x i64], [8 x i64]* @test_case, i32 0, i64 %i_val
  %arr_i_val = load i64, i64* %arr_i_ptr

  %arr_idx_ptr = getelementptr [8 x i64], [8 x i64]* @test_case, i32 0, i64 %idx
  %arr_idx_val = load i64, i64* %arr_idx_ptr

  %cmp3 = icmp slt i64 %arr_i_val, %arr_idx_val
  br i1 %cmp3, label %can_incr_subseq, label %repeat_loop

can_incr_subseq:
  %max_val1 = load i64, i64* %max

  ; index again because we could've recursed and updated subproblem value
  %memo_val2 = load i64, i64* %memo_val_ptr
  %curr_max = add i64 %memo_val2, 1

  %cmp4 = icmp sgt i64 %curr_max, %max_val1

  br i1 %cmp4, label %new_max_found, label %repeat_loop

new_max_found:
  store i64 %curr_max, i64* %max

  br label %repeat_loop

repeat_loop:
  %new_i_val = add i64 %i_val, 1
  store i64 %new_i_val, i64* %i

  br label %loop

after_loop:
  %memo_idx_ptr = getelementptr [8 x i64], [8 x i64]* @memo, i32 0, i64 %idx
  %max_val2 = load i64, i64* %max
  store i64 %max_val2, i64* %memo_idx_ptr

  ret i64 %max_val2
}

define i64 @main(i64 %argc, i8** %arcv) {
  %res = call i64 @lis(i64 7)
  %ans = call i64 @max_in_memo()

  ret i64 %ans
}