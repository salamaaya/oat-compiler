@my_arr1 = global [8 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 4, i64 3, i64 2]
@my_arr2 = global [8 x i64] [i64 1, i64 10, i64 9, i64 7, i64 6, i64 5, i64 4, i64 2]

define i64 @local_max([8 x i64]* %arr, i64 %lo, i64 %hi) {
  %dif = sub i64 %hi, %lo
  %1 = icmp eq i64 %dif, 2
  br i1 %1, label %base_case, label %general_case
base_case:
  %ret_val = add i64 %lo, 1
  ret i64 %ret_val
general_case:
  %2 = add i64 %hi, %lo
  %3 = ashr i64 %2, 1
  
  %i = getelementptr [8 x i64], [8 x i64]* %arr, i32 0, i64 %3
  %ival = load i64, i64* %i

  %4 = sub i64 %3, 1
  %left = getelementptr [8 x i64], [8 x i64]* %arr, i32 0, i64 %4
  %leftVal = load i64, i64* %left

  %5 = add i64 %4, 1
  %right = getelementptr [8 x i64], [8 x i64]* %arr, i32 0, i64 %5
  %rightVal = load i64, i64* %right

  %6 = icmp sge i64 %leftVal, %ival
  br i1 %6, label %rec_call_left, label %check2
  
check2:
  %7 = icmp sge i64 %rightVal, %ival
  br i1 %7, label %rec_call_right, label %is_max
is_max:
  ret i64 %3
rec_call_left:
  %8 = call i64 @local_max([8 x i64]* %arr, i64 %lo, i64 %3)
  ret i64 %8
rec_call_right:
  %9 = call i64 @local_max([8 x i64]* %arr, i64 %3, i64 %hi)
  ret i64 %9
test:
  ret i64 200
}


define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @local_max([8 x i64]* @my_arr1, i64 0, i64 7)
  %test_1 = icmp sge i64 %1, 4 
  br i1 %test_1, label %test2, label %fail

test2:
  %test_2_val = call i64 @local_max([8 x i64]* @my_arr2, i64 0, i64 7)
  %test_2 = icmp sge i64 %1, 2 
  br i1 %test_1, label %pass, label %fail

fail:
  ret i64 0
pass:
  ret i64 1
}