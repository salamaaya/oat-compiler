%arr = type [6 x i64]

@my_arr = global [6 x %arr] [ %arr [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6 ], 
                              %arr [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6 ], 
                              %arr [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6 ], 
                              %arr [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6 ], 
                              %arr [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6 ], 
                              %arr [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6 ] ]


define i64 @main(i64 %argc, i8** %arcv) {
  %2 = call i64 @get_matrix_sum([6 x %arr]* @my_arr, i64 0, i64 0, i64 0)
  ret i64 %2
}


define i64 @get_matrix_sum([6 x %arr]* %matrix, i64 %running_sum, i64 %row, i64 %col) {
    %check_row = icmp eq i64 %row, 6
    br i1 %check_row, label %end, label %check
check:
    %check_col = icmp eq i64 %col, 6
    br i1 %check_col, label %next_row, label %add_col
next_row:
    %nxt_row = add i64 %row, 1
    %rv1 = call i64 @get_matrix_sum([6 x %arr]* %matrix, i64 %running_sum, i64 %nxt_row, i64 0)
    ret i64 %rv1
add_col:
    %c = getelementptr [6 x %arr], [6 x %arr]* %matrix, i64 0, i64 %row, i64 %col
    %val = load i64, i64* %c
    %update_sum = add i64 %running_sum, %val
    %nxt_col = add i64 %col, 1
    %rv2 = call i64 @get_matrix_sum([6 x %arr]* %matrix, i64 %update_sum, i64 %row, i64 %nxt_col)
    ret i64 %rv2
end:
    ret i64 %running_sum
}

