%arr = type [4 x i64]
@tmp = global %arr [ i64 2, i64 7, i64 11, i64 15]
@target = global i64 9

define i64 @two_sum() {
    %len = sub i64 4, 1
    %i = alloca i64
    %j = alloca i64

    br label %outer_loop

    outer_loop:
        store i64 0, i64* %i
        store i64 1, i64* %j
        br label %inner_loop

    inner_loop:
        %idx1 = load i64, i64* %i
        %idx2 = load i64, i64* %j

        %ptr1 = getelementptr %arr, arr* @tmp, i32 0, i64 %idx1
        %ptr2 = getelementptr %arr, arr* @tmp, i32 0, i64 %idx2

        %val1 = load i64, i64* %ptr1
        %val2 = load i64, i64* %ptr2

        %sum = add i64 %val1, %val2
        %tgt = load i64, i64* @target
        %cmp_sum = icmp eq i64 %sum, %tgt
        br i1 %cmp_sum, label %found, label %check_next

    found:
        ret i64 1

    check_next:
        %j_val = load i64, i64* %j
        %j_val_inc = add i64 %j_val, 1
        store i64 %j_val_inc, i64* %j
    
        %cmp2 = icmp slt i64 %j_val_inc, 4
        br i1 %cmp2, label %inner_loop, label %check_outer_loop

    check_outer_loop:
        %i_val = load i64, i64* %i
        %i_val_inc = add i64 %i_val, 1
        store i64 %i_val_inc, i64* %i

        %cmp3 = icmp slt i64 %i_val_inc, 3
        br i1 %cmp3, label %outer_loop, label %not_found    

    not_found:
        ret i64 0    

}


define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @two_sum()
  ret i64 %1
}
