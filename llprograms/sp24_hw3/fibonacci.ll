%arr = type [2 x i64]
@fib_arr = global %arr [i64 1, i64 0]

define i64 @main(i64 %argc, i8** %arcv) {
    %1 = call i64 @rec_fibonacci(i64 5, i64 1)
    ret i64 %1
}

define i64 @rec_fibonacci(i64 %n, i64 %curr) {
    %check_done = icmp eq i64 %curr, %n
    br i1 %check_done, label %end, label %recurse
recurse:
    %pt1 = getelementptr %arr, %arr* @fib_arr, i32 0, i64 0
    %pt2 = getelementptr %arr, %arr* @fib_arr, i32 0, i64 1
    %1 = load i64, i64* %pt1
    %2 = load i64, i64* %pt2
    %3 = add i64 %1, %2
    store i64 %3, i64* %pt1
    store i64 %1, i64* %pt2
    %curr2 = add i64 %curr, 1
    %ret = call i64 @rec_fibonacci(i64 %n, i64 %curr2)
    ret i64 %ret
end:
    %rv_pt = getelementptr %arr, %arr* @fib_arr, i32 0, i64 0
    %rv = load i64, i64* %rv_pt
    ret i64 %rv
}