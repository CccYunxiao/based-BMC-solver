; ModuleID = 'gcd_1_true-unreach-call_true-no-overflow.ll'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define signext i8 @gcd_test(i8 signext %a, i8 signext %b) #0 {
entry:
  %conv = sext i8 %a to i32
  %cmp = icmp slt i32 %conv, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %conv2 = sext i8 %a to i32
  %sub = sub nsw i32 0, %conv2
  %conv3 = trunc i32 %sub to i8
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %a.addr.0 = phi i8 [ %conv3, %if.then ], [ %a, %entry ]
  %conv4 = sext i8 %b to i32
  %cmp5 = icmp slt i32 %conv4, 0
  br i1 %cmp5, label %if.then7, label %if.end11

if.then7:                                         ; preds = %if.end
  %conv8 = sext i8 %b to i32
  %sub9 = sub nsw i32 0, %conv8
  %conv10 = trunc i32 %sub9 to i8
  br label %if.end11

if.end11:                                         ; preds = %if.then7, %if.end
  %b.addr.0 = phi i8 [ %conv10, %if.then7 ], [ %b, %if.end ]
  br label %while.cond

while.cond:                                       ; preds = %while.body, %if.end11
  %b.addr.1 = phi i8 [ %b.addr.0, %if.end11 ], [ %conv17, %while.body ]
  %a.addr.1 = phi i8 [ %a.addr.0, %if.end11 ], [ %b.addr.1, %while.body ]
  %conv12 = sext i8 %b.addr.1 to i32
  %cmp13 = icmp ne i32 %conv12, 0
  br i1 %cmp13, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %conv15 = sext i8 %a.addr.1 to i32
  %conv16 = sext i8 %b.addr.1 to i32
  %rem = srem i32 %conv15, %conv16
  %conv17 = trunc i32 %rem to i8
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret i8 %a.addr.1
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
entry:
  %call = call signext i8 @__VERIFIER_nondet_char()
  %call1 = call signext i8 @__VERIFIER_nondet_char()
  %conv = sext i8 %call1 to i32
  %cmp = icmp sgt i32 %conv, 0
  br i1 %cmp, label %land.lhs.true, label %if.end

land.lhs.true:                                    ; preds = %entry
  %conv3 = sext i8 %call to i32
  %conv4 = sext i8 %call1 to i32
  %rem = srem i32 %conv3, %conv4
  %cmp5 = icmp eq i32 %rem, 0
  br i1 %cmp5, label %if.then, label %if.end

if.then:                                          ; preds = %land.lhs.true
  %conv.i = sext i8 %call to i32
  %cmp.i = icmp slt i32 %conv.i, 0
  br i1 %cmp.i, label %if.then.i, label %if.end.i

if.then.i:                                        ; preds = %if.then
  %conv2.i = sext i8 %call to i32
  %sub.i = sub nsw i32 0, %conv2.i
  %conv3.i = trunc i32 %sub.i to i8
  br label %if.end.i

if.end.i:                                         ; preds = %if.then.i, %if.then
  %a.addr.0.i = phi i8 [ %conv3.i, %if.then.i ], [ %call, %if.then ]
  %conv4.i = sext i8 %call1 to i32
  %cmp5.i = icmp slt i32 %conv4.i, 0
  br i1 %cmp5.i, label %if.then7.i, label %if.end11.i

if.then7.i:                                       ; preds = %if.end.i
  %conv8.i = sext i8 %call1 to i32
  %sub9.i = sub nsw i32 0, %conv8.i
  %conv10.i = trunc i32 %sub9.i to i8
  br label %if.end11.i

if.end11.i:                                       ; preds = %if.then7.i, %if.end.i
  %b.addr.0.i = phi i8 [ %conv10.i, %if.then7.i ], [ %call1, %if.end.i ]
  br label %while.cond.i

while.cond.i:                                     ; preds = %while.body.i, %if.end11.i
  %b.addr.1.i = phi i8 [ %b.addr.0.i, %if.end11.i ], [ %conv17.i, %while.body.i ]
  %a.addr.1.i = phi i8 [ %a.addr.0.i, %if.end11.i ], [ %b.addr.1.i, %while.body.i ]
  %conv12.i = sext i8 %b.addr.1.i to i32
  %cmp13.i = icmp ne i32 %conv12.i, 0
  br i1 %cmp13.i, label %while.body.i, label %gcd_test.exit

while.body.i:                                     ; preds = %while.cond.i
  %conv15.i = sext i8 %a.addr.1.i to i32
  %conv16.i = sext i8 %b.addr.1.i to i32
  %rem.i = srem i32 %conv15.i, %conv16.i
  %conv17.i = trunc i32 %rem.i to i8
  br label %while.cond.i

gcd_test.exit:                                    ; preds = %while.cond.i
  %conv8 = sext i8 %a.addr.1.i to i32
  %conv9 = sext i8 %call1 to i32
  %cmp10 = icmp eq i32 %conv8, %conv9
  %conv11 = zext i1 %cmp10 to i32
  call void @__VERIFIER_assert(i32 %conv11)
  br label %if.end

if.end:                                           ; preds = %gcd_test.exit, %land.lhs.true, %entry
  ret i32 0
}

declare signext i8 @__VERIFIER_nondet_char() #1

declare void @__VERIFIER_assert(i32) #1

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.0 (tags/RELEASE_380/final)"}
