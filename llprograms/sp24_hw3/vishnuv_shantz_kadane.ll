; To try out different cases, add them below as global and replace the values in the getelementptr in @main with the new globals.
@input_array1 = global [8 x i64] [i64 -2, i64 -3, i64 4, i64 -1, i64 -2, i64 1, i64 5, i64 -3]
@size1 = global i64 8

@input_array2 = global [5 x i64] [i64 1, i64 2, i64 3, i64 -2, i64 5]
@size2 = global i64 5

@input_array3 = global [9 x i64] [i64 -2, i64 1, i64 -3, i64 4, i64 -1, i64 2, i64 1, i64 -5, i64 4]
@size3 = global i64 9

define i64 @max_of_two(i64 %num1, i64 %num2) {
entry:
    %cmp = icmp sgt i64 %num1, %num2
    br i1 %cmp, label %return_num1, label %return_num2
return_num1:
    ret i64 %num1
return_num2:
    ret i64 %num2
}   

define i64 @kadane(i64* %array, i64 %length) {
    %max_so_far = alloca i64
    %max_ending_here = alloca i64
    store i64 -2147483648, i64* %max_so_far
    store i64 0, i64* %max_ending_here

    %i = alloca i64
    store i64 0, i64* %i
    br label %loop

loop:
    %i_val = load i64, i64* %i
    %cond = icmp slt i64 %i_val, %length
    br i1 %cond, label %body, label %end

body:
    %current = getelementptr i64, i64* %array, i64 %i_val
    %current_val = load i64, i64* %current
    %max_ending_here_val = load i64, i64* %max_ending_here
    %new_max_ending_here = add i64 %max_ending_here_val, %current_val
    %max_ending_here_next = call i64 @max_of_two(i64 %new_max_ending_here, i64 0)
    store i64 %max_ending_here_next, i64* %max_ending_here

    %max_so_far_val = load i64, i64* %max_so_far
    %max_so_far_next = call i64 @max_of_two(i64 %max_ending_here_next, i64 %max_so_far_val)
    store i64 %max_so_far_next, i64* %max_so_far

    %i_next = add i64 %i_val, 1
    store i64 %i_next, i64* %i
    br label %loop

end:
    %result = load i64, i64* %max_so_far
    ret i64 %result
}

define i64 @main(i64 %argc, i8** %argv) {
    ; CHANGE THE VALUES IN THE NEXT TWO LINES FOR NEW TEST CASES
    ; Remember to change the sizes of the input array in the first gep too
    %array_ptr = getelementptr [9 x i64], [9 x i64]* @input_array3, i64 0, i64 0
    %size_ptr = getelementptr i64, i64* @size3, i64 0

    %size_val = load i64, i64* %size_ptr
    %main_result = call i64 @kadane(i64* %array_ptr, i64 %size_val)
    ret i64 %main_result
}
