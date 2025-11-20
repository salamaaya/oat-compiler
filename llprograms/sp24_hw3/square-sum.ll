%arr = type [5 x i64]

@tmp = global %arr [ i64 2, i64 4, i64 6, i64 8, i64 10 ]

define void @mapsquarehelper(%arr* %input, i64 %index) {
    %1 = icmp eq i64 %index, 5
    br i1 %1, label %ret1, label %recurse
    ret1:
        ret void
    recurse:
        %2 = getelementptr %arr, %arr* %input, i64 0, i64 %index
        %3 = load i64, i64* %2
        %4 = call i64 @square(i64 %3)
        store i64 %4, i64* %2
        %5 = add i64 %index, 1
        call void @mapsquarehelper(%arr* %input, i64 %5)
        ret void
}

define void @mapsquare(%arr* %input) {
    call void @mapsquarehelper(%arr* %input, i64 0)
    ret void
}

define i64 @square(i64 %x) {
    %1 = mul i64 %x, %x 
    ret i64 %1
}


define i64 @main(i64 %argc, i8** %arcv) {
    call void @mapsquare(%arr* @tmp)

    %1 = getelementptr %arr, %arr* @tmp, i64 0, i64 0
    %2 = getelementptr %arr, %arr* @tmp, i64 0, i64 1
    %3 = getelementptr %arr, %arr* @tmp, i64 0, i64 2
    %4 = getelementptr %arr, %arr* @tmp, i64 0, i64 3
    %5 = getelementptr %arr, %arr* @tmp, i64 0, i64 4
    
    %6 = load i64, i64* %1
    %7 = load i64, i64* %2
    %8 = load i64, i64* %3
    %9 = load i64, i64* %4
    %10 = load i64, i64* %5

    %11 = add i64 %6, %7
    %12 = add i64 %11, %8
    %13 = add i64 %12, %9
    %14 = add i64 %13, %10

    ret i64 %14
}
