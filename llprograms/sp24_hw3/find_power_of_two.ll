%consList = type { i64, %consList* }

@nonPowerOfTwoElem = global %consList { i64 9, %consList* null }
@powerOfTwoElem = global %consList { i64 64, %consList* @nonPowerOfTwoElem }
@head = global %consList { i64 31, %consList* @powerOfTwoElem }

define i64 @numOneBits(i64 %n) {
  %isZero = icmp eq i64 %n, 0
  br i1 %isZero, label %retZero, label %rec
retZero:
  ret i64 0
rec:
  %shifted = lshr i64 %n, 1
  %recResult = call i64 @numOneBits(i64 %shifted)
  %lsb = and i64 %n, 1
  %result = add i64 %recResult, %lsb
  ret i64 %result
}

define i1 @isPowerOfTwo(i64 %n) {
  %isNotPositive = icmp sle i64 %n, 0
  br i1 %isNotPositive, label %retFalse, label %continue
retFalse:
  ret i1 0
continue:
  %numOnes = call i64 @numOneBits(i64 %n)
  %hasSingleOneBit = icmp eq i64 %numOnes, 1
  br i1 %hasSingleOneBit, label %retTrue, label %retFalse
retTrue:
  ret i1 1
}

define i64 @findFirstPowerOfTwo(%consList* %l) {
  %isNull = icmp eq %consList* %l, null
  br i1 %isNull, label %retFalse, label %continue
retFalse:
  ret i64 0
continue:
  %currNumPtr = getelementptr %consList, %consList* %l, i32 0, i32 0
  %currNum = load i64, i64* %currNumPtr
  %isPowTwo = call i1 @isPowerOfTwo(i64 %currNum)
  br i1 %isPowTwo, label %retTrue, label %rec
retTrue:
  ret i64 %currNum
rec:
  %nextPtr = getelementptr %consList, %consList* %l, i32 0, i32 1
  %next = load %consList*, %consList** %nextPtr
  %recResult = call i64 @findFirstPowerOfTwo(%consList* %next)
  ret i64 %recResult
}

define i64 @main(i64 %argc, i8** %arcv) {
  %powTwoValue = call i64 @findFirstPowerOfTwo(%consList* @head)
  ret i64 %powTwoValue
}