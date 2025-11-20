%arraystruct = type {[9 x i64]}

; 8,7,2,1,0,9,3,2,1
@gtest1 = global %arraystruct {[9 x i64] [i64 8, i64 7, i64 2, i64 1, i64 0, i64 9, i64 3, i64 2, i64 1]}
@ans1 = global %arraystruct {[9 x i64] [i64 0, i64 1, i64 1, i64 2, i64 2, i64 3, i64 7, i64 8, i64 9]}
@gtest2 = global %arraystruct {[9 x i64] [i64 1, i64 5, i64 3, i64 8, i64 2, i64 6, i64 9, i64 4, i64 7]}
@ans2 = global %arraystruct {[9 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9]}
@gtest3 = global %arraystruct {[9 x i64] [i64 9, i64 3, i64 6, i64 1, i64 5, i64 2, i64 7, i64 8, i64 4]}
@ans3 = global %arraystruct {[9 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9]}
@gtest4 = global %arraystruct {[9 x i64] [i64 5, i64 2, i64 8, i64 9, i64 1, i64 4, i64 6, i64 3, i64 7]}
@ans4 = global %arraystruct {[9 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9]}


; @gtest1 = global %arraystruct [i64 2, i64 3, i64 1]
; @ans1 = global %arraystruct [i64 1, i64 2, i64 3]

define i1 @eq9(%arraystruct* %arr1, %arraystruct* %arr2) {
  %lengthptr = alloca i64
  store i64 9, i64* %lengthptr
  %length = load i64, i64* %lengthptr
  %iptr = alloca i64
  store i64 0, i64* %iptr
  br label %loop_entry
loop_entry:
  %iteri = load i64, i64* %iptr
  %cmpll = icmp slt i64 %iteri, %length
  br i1 %cmpll, label %loop_body, label %loop_exit_s
loop_body:
  %arri1ptr = getelementptr %arraystruct, %arraystruct* %arr1, i32 0, i32 0, i64 %iteri
  %arri1 = load i64, i64* %arri1ptr
  %arri2ptr = getelementptr %arraystruct, %arraystruct* %arr2, i32 0, i32 0, i64 %iteri
  %arri2 = load i64, i64* %arri2ptr
  %cmp12 = icmp eq i64 %arri1, %arri2
  br i1 %cmp12, label %loop_next, label %loop_exit_f
loop_next:
  %i = load i64, i64* %iptr
  %iplus = add i64 %i, 1
  store i64 %iplus, i64* %iptr
  br label %loop_entry
loop_exit_s:
  ret i1 1
loop_exit_f:
  ret i1 0
}

define void @swap(i64* %0, i64* %1) {
  %int0 = load i64, i64* %0
  %int1 = load i64, i64* %1
  store i64 %int0, i64* %1
  store i64 %int1, i64* %0
  ret void
}

define i64 @partition(%arraystruct* %arr, i64 %lowint, i64 %highint) {
  ; %highint = load i64, i64* %high
  ; %lowint = load i64, i64* %low
  %pivotptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %highint
  %pivotint = load i64, i64* %pivotptr
  %i = sub i64 %lowint, 1
  %iptr = alloca i64
  store i64 %i, i64* %iptr
  %jptr = alloca i64
  store i64 %lowint, i64* %jptr
  br label %loop_entry

loop_entry:
  %iterj = load i64, i64* %jptr
  %cmphigh = icmp slt i64 %iterj, %highint
  br i1 %cmphigh, label %loop_body, label %loop_exit

loop_body:
  %arrj = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %iterj
  %arrjval = load i64, i64* %arrj
  %cmppivot = icmp sle i64 %arrjval, %pivotint
  br i1 %cmppivot, label %loop_swap, label %loop_next

loop_swap:
  %ival = load i64, i64* %iptr
  %iplus = add i64 1, %ival
  store i64 %iplus, i64* %iptr
  %iteri = load i64, i64* %iptr
  %arrj1 = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %iterj
  %arri = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %iteri
  call void @swap(i64* %arri, i64* %arrj1)
  br label %loop_next

loop_next:
  %jplus = add i64 %iterj, 1
  store i64 %jplus, i64* %jptr
  br label %loop_entry

loop_exit:
  %ifin = load i64, i64* %iptr
  %ifinplus = add i64 1, %ifin
  %arrifin = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0,i64 %ifinplus
  %arrhigh = getelementptr %arraystruct, %arraystruct* %arr, i32 0,i32 0, i64 %highint
  call void @swap(i64* %arrifin, i64* %arrhigh)
  ret i64 %ifinplus
}

define void @quicksort(%arraystruct* %arr, i64 %lowint, i64 %highint) {
  %cmplh = icmp slt i64 %lowint, %highint
  br i1 %cmplh, label %recursion, label %exit
recursion:
  %pivot = call i64 @partition(%arraystruct* %arr, i64 %lowint, i64 %highint)
  %pivots1 = sub i64 %pivot, 1
  %pivota1 = add i64 %pivot, 1
  call void @quicksort(%arraystruct* %arr, i64 %lowint, i64 %pivots1)
  call void @quicksort(%arraystruct* %arr, i64 %pivota1, i64 %highint)
  br label %exit
exit:
  ret void
}

define i1 @main(i64 %argc, i8** %arcv) {
  call void @quicksort(%arraystruct* @gtest1, i64 0, i64 8)
  %res1 = call i1 @eq9(%arraystruct* @gtest1, %arraystruct* @ans1)
  call void @quicksort(%arraystruct* @gtest2, i64 0, i64 8)
  %res2 = call i1 @eq9(%arraystruct* @gtest2, %arraystruct* @ans2)
  call void @quicksort(%arraystruct* @gtest3, i64 0, i64 8)
  %res3 = call i1 @eq9(%arraystruct* @gtest3, %arraystruct* @ans3)
  call void @quicksort(%arraystruct* @gtest4, i64 0, i64 8)
  %res4 = call i1 @eq9(%arraystruct* @gtest4, %arraystruct* @ans4)
  %resagg1 = and i1 %res1, %res2
  %resagg2 = and i1 %resagg1, %res3
  %resagg3 = and i1 %resagg1, %res4
  ret i1 1
}