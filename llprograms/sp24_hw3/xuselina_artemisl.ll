%array_ty = type [7 x i64]

@array = global %array_ty [i64 23, i64 10, i64 20, i64 11, i64 12, i64 6, i64 7]
@sorted_array = global %array_ty [i64 6, i64 7, i64 10, i64 11, i64 12, i64 20, i64 23]

define void @flip(%array_ty* %array, i64 %len) {
  %start = alloca i64
  %end = alloca i64
  %temp = alloca i64
  store i64 0, i64* %start
  store i64 %len, i64* %end
  br label %setup_flip

setup_flip:
  %1 = load i64, i64* %start
  %2 = load i64, i64* %end
  %cmp1 = icmp slt i64 %1, %2
  br i1 %cmp1, label %flip_op, label %end_flip

flip_op:
  %3 = load i64, i64* %start
  %s_val_ptr = getelementptr %array_ty, %array_ty* %array, i32 0, i64 %3
  %s_val = load i64, i64* %s_val_ptr
  store i64 %s_val, i64* %temp
  %4 = load i64, i64* %end
  %e_val_ptr = getelementptr %array_ty, %array_ty* %array, i32 0, i64 %4
  %e_val = load i64, i64* %e_val_ptr
  store i64 %e_val, i64* %s_val_ptr
  %5 = load i64, i64* %temp
  store i64 %5, i64* %e_val_ptr
  %6 = load i64, i64* %start
  %7 = add i64 %6, 1
  store i64 %7, i64* %start
  %8 = load i64, i64* %end
  %9 = sub i64 %8, 1
  store i64 %9, i64* %end
  br label %setup_flip

end_flip:
  ret void
}


define i64 @findMax(%array_ty* %array, i64 %len) {
  %index = alloca i64
  %max = alloca i64
  %temp = alloca i64
  store i64 0, i64* %index
  br label %setup_cmp

setup_cmp:
  %1 = load i64, i64* %index
  %cmp2 = icmp slt i64 %1, %len
  br i1 %cmp2, label %compare, label %end

compare:
  %2 = load i64, i64* %index
  %ptr = getelementptr %array_ty, %array_ty* %array, i32 0, i64 %2
  %val = load i64, i64* %ptr
  %3 = load i64, i64* %max
  %cmp3 = icmp slt i64 %val, %3
  br i1 %cmp3, label %end, label %update_max

update_max:
  %4 = load i64, i64* %temp
  store i64 %4, i64* %ptr
  %5 = load i64, i64* %max
  store i64 %5, i64* %temp
  %6 = load i64, i64* %index
  %7 = add i64 %6, 1
  store i64 %7, i64* %index
  br label %setup_cmp

end:
  %8 = load i64, i64* %max
  ret i64 %8
}

define void @pancakeSort(%array_ty %array, i64 %len) {
  %index = alloca i64 
  store i64 %len, i64* %index
  br label %start_pancake

start_pancake:
  %1 = load i64, i64* %index
  %cmp3 = icmp sgt i64 %1, 1
  br i1 %cmp3, label %pancake_op, label %end_pancake

pancake_op:
  %max = call i64 @findMax(%array_ty* @array, i64 %len)
  %in = load i64, i64* %index
  %index_m_1 = sub i64 %in, 1
  %cmp4 = icmp ne i64 %max, %index_m_1
  br i1 %cmp4, label %flip, label %end_flip

flip:
  call void @flip(%array_ty* @array, i64 %max)
  call void @flip(%array_ty* @array, i64 %index_m_1)
  br label %end_flip


end_flip:
%2 = load i64, i64* %index
  %3 = sub i64 %2, 1
  store i64 %2, i64* %index
  br label %start_pancake

  end_pancake:
  ret void

}

define i64 @isEqual(%array_ty* %array, %array_ty* %sorted_array) {
  %index = alloca i64
  store i64 0, i64* %index
  br label %iterate

iterate:
%1 = load i64, i64* %index
  %cmp5 = icmp slt i64 %1, 7

  br i1 %cmp5, label %check, label %equal

check:
%2 = load i64, i64* %index
  %ptr = getelementptr %array_ty, %array_ty* %array, i32 0, i64 %2
  %val = load i64, i64* %ptr
  %3 = load i64, i64* %index
  %ptr2 = getelementptr %array_ty, %array_ty* %sorted_array, i32 0, i64 %3
  %val2 = load i64, i64* %ptr2
  %cmp6 = icmp eq i64 %val, %val2
  br i1 %cmp6, label %move_pointer, label %not_equal

move_pointer:
  %4 = load i64, i64* %index
  %5 = add i64 %4, 1
  store i64 %5, i64* %index

  br label %iterate

equal:
  ret i64 0

not_equal:
  ret i64 1

}

define i64 @main(i64 %argc, i8** %arcv) {
  ;call void @pancakeSort(%array_ty* @array, i64 7)
  ;%result = call i64 @isEqual(%array_ty* @array, %array_ty* @sorted_array)
  ;ret i64 %result 
  ret i64 0
    
}