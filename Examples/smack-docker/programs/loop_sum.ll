; ModuleID = 'loop_sum.bc'
source_filename = "loop_sum.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 !dbg !7 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !11, metadata !DIExpression()), !dbg !12
  store i32 0, i32* %2, align 4, !dbg !12
  call void @llvm.dbg.declare(metadata i32* %3, metadata !13, metadata !DIExpression()), !dbg !15
  store i32 0, i32* %3, align 4, !dbg !15
  br label %4, !dbg !16

4:                                                ; preds = %11, %0
  %5 = load i32, i32* %3, align 4, !dbg !17
  %6 = icmp slt i32 %5, 5, !dbg !19
  br i1 %6, label %7, label %14, !dbg !20

7:                                                ; preds = %4
  %8 = load i32, i32* %3, align 4, !dbg !21
  %9 = load i32, i32* %2, align 4, !dbg !23
  %10 = add nsw i32 %9, %8, !dbg !23
  store i32 %10, i32* %2, align 4, !dbg !23
  br label %11, !dbg !24

11:                                               ; preds = %7
  %12 = load i32, i32* %3, align 4, !dbg !25
  %13 = add nsw i32 %12, 1, !dbg !25
  store i32 %13, i32* %3, align 4, !dbg !25
  br label %4, !dbg !26, !llvm.loop !27

14:                                               ; preds = %4
  %15 = load i32, i32* %2, align 4, !dbg !30
  %16 = icmp eq i32 %15, 10, !dbg !31
  %17 = zext i1 %16 to i32, !dbg !31
  %18 = call i32 (i32, ...) bitcast (i32 (...)* @assert to i32 (i32, ...)*)(i32 %17), !dbg !32
  ret i32 0, !dbg !33
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

declare dso_local i32 @assert(...) #2

attributes #0 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nosync nounwind readnone speculatable willreturn }
attributes #2 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "Ubuntu clang version 12.0.1-++20211029101322+fed41342a82f-1~exp1~20211029221816.4", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "loop_sum.c", directory: "/programs")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"Ubuntu clang version 12.0.1-++20211029101322+fed41342a82f-1~exp1~20211029221816.4"}
!7 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 3, type: !8, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!8 = !DISubroutineType(types: !9)
!9 = !{!10}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DILocalVariable(name: "sum", scope: !7, file: !1, line: 4, type: !10)
!12 = !DILocation(line: 4, column: 7, scope: !7)
!13 = !DILocalVariable(name: "i", scope: !14, file: !1, line: 5, type: !10)
!14 = distinct !DILexicalBlock(scope: !7, file: !1, line: 5, column: 3)
!15 = !DILocation(line: 5, column: 12, scope: !14)
!16 = !DILocation(line: 5, column: 8, scope: !14)
!17 = !DILocation(line: 5, column: 19, scope: !18)
!18 = distinct !DILexicalBlock(scope: !14, file: !1, line: 5, column: 3)
!19 = !DILocation(line: 5, column: 21, scope: !18)
!20 = !DILocation(line: 5, column: 3, scope: !14)
!21 = !DILocation(line: 6, column: 12, scope: !22)
!22 = distinct !DILexicalBlock(scope: !18, file: !1, line: 5, column: 31)
!23 = !DILocation(line: 6, column: 9, scope: !22)
!24 = !DILocation(line: 7, column: 3, scope: !22)
!25 = !DILocation(line: 5, column: 27, scope: !18)
!26 = !DILocation(line: 5, column: 3, scope: !18)
!27 = distinct !{!27, !20, !28, !29}
!28 = !DILocation(line: 7, column: 3, scope: !14)
!29 = !{!"llvm.loop.mustprogress"}
!30 = !DILocation(line: 8, column: 10, scope: !7)
!31 = !DILocation(line: 8, column: 14, scope: !7)
!32 = !DILocation(line: 8, column: 3, scope: !7)
!33 = !DILocation(line: 9, column: 3, scope: !7)
