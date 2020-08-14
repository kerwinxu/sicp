#lang sicp

(define (eval exp env)   ; 原先这个下边边分析边执行
  ((analyze exp) env))   ; 现在这个会调用分析,然后他的参数是env,环境变量,根据这个再执行的。
; 然后下边是这个分析
; 可以看到基本对应原先的eval
(define (analyze exp)
  (cond ((self-evaluating? exp) (analyze-self-evaluating exp))
        ((quoted? exp) (analyze-quoted exp))
        ((variable? exp) (analyze-variable exp))
        ((assignment? exp) (analyze-assignment exp))
        ((definition? exp) (analyze-definition exp))
        ((if? exp) (analyze-if exp))
        ((lambda? exp) (analyze-lambda exp))
        ((begin? exp) (analyze-sequence (begin-actions exp)))
        ((cond? exp) (analyze (cond->if exp)))
        ((application? exp) (analyze-application exp))
        (else (error "Unknown expression type: ANALYZE" exp))))

; 如下对应上边的分支
;
(define (analyze-self-evaluating exp)   ; 对于自求值的。
  (lambda (env) exp))                   ; 返回他自己喽
;
(define (analyze-quoted exp)            ; 对于引证
  (let ((qval (text-of-quotation exp))) ; 取得引用体,
    (lambda (env) qval)))               ; 返回这个引用体
;
(define (analyze-variable exp)                     ; 对于变量
  (lambda (env) (lookup-variable-value exp env)))  ; 依然在执行阶段去搜索,这个依赖环境变量的。

; 变量的定义
(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))            ; 变量,提前分析
        (vproc (analyze (assignment-value exp))))  ; 变量值,提前分析,
    (lambda (env)
      (set-variable-value! var (vproc env) env)    ; 这里执行。
      'ok)))
; 过程的定义,
(define (analyze-definition exp)
  (let ((var (definition-variable exp))           ; 变量,提前分析
        (vproc (analyze (definition-value exp)))) ; 变量值,提前分析
    (lambda (env)
      (define-variable! var (vproc env) env)      ; 这里执行。
      'ok)))
; 
(define (analyze-if exp)
  (let ((pproc (analyze (if-predicate exp)))      ; 用analyze提前分析出条件,
        (cproc (analyze (if-consequent exp)))     ; 为真的时候执行的表达式
        (aproc (analyze (if-alternative exp))))   ; 为假的时候执行的表达式
    (lambda (env) (if (true? (pproc env))
                      (cproc env)
                      (aproc env)))))
; 
(define (analyze-lambda exp)
  (let ((vars (lambda-parameters exp))                ; 参数
        (bproc (analyze-sequence (lambda-body exp)))) ; 只分析一次body
    (lambda (env) (make-procedure vars bproc env))))  ; 返回这个过程可以多次执行。
;
(define (analyze-sequence exps)                ; 表达式的分析。
  (define (sequentially proc1 proc2)        ; 这个函数是
    (lambda (env) (proc1 env) (proc2 env))) ; 顺序的执行2个过程
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc      ; 如果是最后一个,就返回这个值当作整个表达式序列的值。
        (loop (sequentially first-proc (car rest-procs)) ; 这个是不断的将过程连接起来。
              (cdr rest-procs))))
  (let ((procs (map analyze exps)))                     
    (if (null? procs) (error "Empty sequence: ANALYZE")) ; 首先从总体上判断是否是空的表达式。
    (loop (car procs) (cdr procs)))) ; 递归调用表达式。

;
(define (analyze-application exp)               ; 分析程序
  (let ((fproc (analyze (operator exp)))        ; 获得实际应用的对象。
        (aprocs (map analyze (operands exp))))  ; 分析参数
    (lambda (env)                               ; 返回一个需要参数为环境的过程
      (execute-application
       (fproc env)
       (map (lambda (aproc) (aproc env))        ; 这个map会返回实际参数。
            aprocs)))))
(define (execute-application proc args)         ; 执行过程
  (cond ((primitive-procedure? proc)            ; 简单过程吗
         (apply-primitive-procedure proc args))
        ((compound-procedure? proc)      ; 复杂过程
         ((procedure-body proc)          ; 取得函数体,执行后边的过程。
          (extend-environment              ; 创建一个环境
           (procedure-parameters proc)     ; 变量名
           args                            ; 变量值
           (procedure-environment proc)))) ; 这个proc的环境就是这个要构造的application的环境。
        (else
         (error "Unknown procedure type: EXECUTE-APPLICATION"
                proc))))




;(define (eval exp env)
;  (cond ((self-evaluating? exp) exp)                      ; 自求值，数字或者字符串
;        ((variable? exp) (lookup-variable-value exp env)) ; 在环境中找出变量
;        ((quoted? exp) (text-of-quotation exp))           ; '
;        ((assignment? exp) (eval-assignment exp env))     ; 变量的赋值（定义）。
;        ((definition? exp) (eval-definition exp env))     ; 定义的。
;        ((if? exp) (eval-if exp env))                           ; if 语句
;        ((lambda? exp) (make-procedure (lambda-parameters exp)  ; lambda，转化为可以应用的过程
;                                       (lambda-body exp)
;                                       env))
;        ((begin? exp)                                    ; begin语句，求值一系列的表达式，按照它们出现的顺序。
;         (eval-sequence (begin-actions exp) env))
;        ((cond? exp) (eval (cond->if exp) env))          ; cond语句
;        ((application? exp)                              ; 函数过程。
;         (myapply (eval (operator exp) env)              ; 这里是生成函数名，但这个也是要递归处理的，函数名是可能由表达式生成的。 
;                (list-of-values (operands exp) env)))    ; 生成参数
;        (else
;         (error "Unknown expression type: EVAL" exp))))

; 清注意： 原文中是apply，这个跟系统原先的apply冲突，毕竟我需要调用系统的apply，所以这里改名字了。
; 当然，也可以先保存原先的引用 ; (define apply-in-underlying-scheme apply) ，然后再修改。不过我没测试过。
; 我优先的方法是，尽量避免重复名字。
(define (myapply procedure arguments)         ; 参数，一个是过程，一个是该过程应该去实际应用的表。
  (cond ((primitive-procedure? procedure)                   ; 基本过程
         (apply-primitive-procedure procedure arguments))   ; 只是简单的执行后边的东西。
        ((compound-procedure? procedure)                    ; 复合过程，需要建立相应的环境。
         (eval-sequence                         ; 执行一个序列，相当于begin吧。
          (procedure-body procedure)            ; 一堆表达式
          (extend-environment                   ; 创建一个新的环境。
           (procedure-parameters procedure)     ; 变量名
           arguments                            ; 变量值
           (procedure-environment procedure)))) ; 上一层环境。
        (else      ; 其他情况
         (error    ; 就是错误啦
          "Unknown procedure type: APPLY" procedure))))

; 过程参数，
; eval在处理过程引用时用 如下的生成实际的参数表
(define (list-of-values exps env)
  (if (no-operands? exps)                    ; 首先判断是否有参数
      '()                                    ; 没参数返回空表
      (cons (eval (first-operand exps) env)  ; 这里表示有参数,用eval来求出实际的值
            (list-of-values (rest-operands exps) env))))  ; 递归处理其他的参数。
; 条件
; if条件的
(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env)) ; 求值if表达式,
      (eval (if-consequent exp) env)        ; 如果为真,就执行这个
      (eval (if-alternative exp) env)))     ; 这里表示为假就执行的。

; 序列,一个表达式序列和一个环境为参数,
(define (eval-sequence exps env)
  (cond ((last-exp? exps)             ; 如果是最后一个表达式,
         (eval (first-exp exps) env)) ; 求值这个表达式,返回结果。
        (else                         ; 其他情况
         (eval (first-exp exps) env)  ; 求值这个表达式,
         (eval-sequence (rest-exps exps) env)))) ; 然后其他表达式递归处理

; 赋值和定义
(define (eval-assignment exp env)                   
  (set-variable-value! (assignment-variable exp)            ; set-variable-value!将有关的变量和值安置到指定的环境里。
                       (eval (assignment-value exp) env)    ; 计算需要赋的值
                       env)                                 ; 在指定的环境。
  'ok)
; 定义过程类似
(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

; 表达式的表示,如下是几个语法规范
(define (self-evaluating? exp)    ; 自求值表达式只有
  (cond ((number? exp) true)      ; 数字
        ((string? exp) true)      ; 字符串
        (else false)))

(define (tagged-list? exp tag)  ; 确定一个表的开始是不是某个给定的符号。
  (if (pair? exp)               ; 这个是括号表达式
      (eq? (car exp) tag)       ; 第一项目是tag吗?,比如exp是(set! <var> <value>),那么这个是比较set!是否跟参数中的tag是一样的。
      false))

(define (variable? exp) (symbol? exp))  ; 是否变量
(define (quoted? exp) (tagged-list? exp 'quote))  ; 引号表达式的形式是(quete <text-of-quotation>) ,'a 实际上是(quote a)
(define (text-of-quotation exp) (cadr exp))       ; 引用表达式是(quete a b c) = ('a b c)，所以，这里引用体是,这个引用只是后边第一个被转义吧，也就是a。

; 赋值的形式是(set! <var> <value>)
(define (assignment? exp) (tagged-list? exp 'set!))  
(define (assignment-variable exp) (cadr exp))  ; 是取得上边的<var>
(define (assignment-value exp) (caddr exp))    ; 去取得上边的<value>

; 定义的基本形式
; (define <var> <value>)
; 或者
; (define (⟨var⟩ ⟨parameter1⟩ . . . ⟨parametern⟩)
;      ⟨body⟩)
; 后一种是如下的包装
;(define ⟨var⟩
;  (lambda (⟨parameter1⟩ . . . ⟨parametern⟩)
;    ⟨body⟩))
(define (definition? exp) (tagged-list? exp 'define))  ; 是否是定义。
(define (definition-variable exp)  ; 取得名字
  (if (symbol? (cadr exp))         ; 如果是符号
      (cadr exp)                   ; 就返回这个符号，格式是这种 (define <var> <value>)
      (caadr exp)))                ; 那么格式就是这种 (define (⟨var⟩ ⟨parameter1⟩ . . . ⟨parametern⟩)  <body>) 
(define (definition-value exp)     ; 取得值，定义的值或者过程体
  (if (symbol? (cadr exp))         ; 同样需要判断是否是符号，毕竟2种格式呢。
      (caddr exp)
      (make-lambda (cdadr exp)     ; formal parameters，如果是过程，这个会生成匿名函数。
                   (cddr exp))))   ; body

; lambda 表达式是如下的表 格式是 (lambda (参数表) (函数体))
(define (lambda? exp) (tagged-list? exp 'lambda))  ; 判断第一个是否是lambda
(define (lambda-parameters exp) (cadr exp))        ; 第二个是参数表
(define (lambda-body exp) (cddr exp))              ; 第三个是函数体
; lambda的构造过程，也就是构造这个格式('lambda (参数表) (函数体))
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

; if相关的，格式是(if (条件) (真的时候执行) (假的时候执行))
(define (if? exp) (tagged-list? exp 'if))  ; 
(define (if-predicate exp) (cadr exp))     ; if 中的条件
(define (if-consequent exp) (caddr exp))   ; if为真执行的
(define (if-alternative exp)               ; if为假执行的
  (if (not (null? (cdddr exp)))            ; 这部分可以为空的,这里判断一下。
      (cadddr exp)
      'false))
; if的构造过程,
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative)) ; 这行可以对比上边的if-predicate等,就可以看出来分别取得什么了。

; begin表达式
(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))          ; 所有需要执行的表达式。这个是复数。
(define (last-exp? seq) (null? (cdr seq)))      ; 判断是否是最后一个。
(define (first-exp seq) (car seq))              ; 第一个，就是car
(define (rest-exps seq) (cdr seq))              ; 其他所有的，是cdr
; 将一个序列转化为begin表达式
(define (sequence->exp seq)                     ; 将一个序列转化为表达式，
  (cond ((null? seq) seq)                       ; 如果为空，就他自己
        ((last-exp? seq) (first-exp seq))       ; 如果只有一个，也是自己，
        (else (make-begin seq))))               ; 其他情况，转成begin表达式。
(define (make-begin seq) (cons 'begin seq))     ; 这个是转化为begin表达式。
; 过程应用，car是运算符，cdr是运算对象的表。
(define (application? exp) (pair? exp))  ; （是过程应用
(define (operator exp) (car exp))        ; 取得函数名
(define (operands exp) (cdr exp))        ; 取得函数体
(define (no-operands? ops) (null? ops))  ; 没有运算符？
(define (first-operand ops) (car ops))   ; 第一个操作数
(define (rest-operands ops) (cdr ops))   ; 其他操作数

(define (unassigned? val) (eq? val '*unassigned*))  ; 判断是否是未定义。

; 将cond规约成if，cond可以用嵌套的if表达。
(define (cond? exp) (tagged-list? exp 'cond))    ; 判断
(define (cond-clauses exp) (cdr exp))            ; cond过程体，cdr，应该是'cond后所有的
(define (cond-else-clause? clause)               ; cond最后不是有个else吗？
  (eq? (cond-predicate clause) 'else))           ; 这里判断是否是else的
(define (cond-predicate clause) (car clause))    ; 第一个是判断的
(define (cond-actions clause) (cdr clause))      ; 其他是执行的
(define (cond->if exp) (expand-clauses (cond-clauses exp)))  ; 是所有的过程体

(define (expand-clauses clauses)
  (if (null? clauses)                 ; 首先判断是否结束吧。
      'false ; no else clause
      (let ((first (car clauses))     ; 先处理第一个，
            (rest (cdr clauses)))     ; 其他的递归。
        (if (cond-else-clause? first) ; 判断是否是else，因为else特殊。
            (if (null? rest)          ; else是最后一个啦。
                (sequence->exp (cond-actions first))       ; 将其他执行的转变为begin表达式。
                (error "ELSE clause isn't last: COND->IF"  ; else不是最后一个，
                       clauses))
            (make-if (cond-predicate first)                ; 构造if语句，这里是条件。
                     (sequence->exp (cond-actions first))  ; 为真的时候执行
                     (expand-clauses rest))))))            ; 为假的时候执行，这里用递归，实现的是嵌套if

; 求值器的数据结构。
; 谓词的检测
(define (true? x) (not (eq? x false)))
(define (false? x) (eq? x false))
; 过程的表示
; 是否是一个基本过程。
(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))
; 将给定的过程应用于表args里的参数值，并返回这一应用的结果。
; 如下的这个是简单过程。
(define (apply-primitive-procedure proc args) 
  (apply-in-underlying-scheme
   (primitive-implementation proc) args))
; 复合过程的构造函数
(define (make-procedure parameters body env)
  (list 'procedure parameters (scan-out-defines body) env))       ; 复合过程的格式是这个。
(define (compound-procedure? p)                ; 判断是否为复合过程。
  (tagged-list? p 'procedure))
; 如下分别取得复合过程的3个部分。
(define (procedure-parameters p) (cadr p))     ; 取得参数表
(define (procedure-body p) (caddr p))          ; 取得函数体
(define (procedure-environment p) (cadddr p))  ; 取得环境

; 如下是支持内部定义的部分

(define UNASSIGNED (quote '*unassigned*))

(define (scan-out-defines body)
  " Translate the form:
  ((define u <e1>)
   (define v <e2>)
   <e3>)
  to:
  ((let ((u '*unassigned*)
         (v '*unassigned*))
     (set! u <e1>)
     (set! v <e2>)
     <e3>))"
  (let ((vars '())
        (vals '()))
    (define new-body 
      (map (lambda (exp)             ; map，对序列的高阶函数，这里是对原先的body
             (if (definition? exp)   ; 筛选那些内部定义中是define的
                 (begin (set! vars (cons (definition-variable exp) vars))  ; 这2个set!是修改操作。通过修改完成添加。
                        (set! vals (cons UNASSIGNED vals))
                        (list 'set! (definition-variable exp) (definition-value exp))) ; 这个是作为map的返回，
                 exp))
           body))
    (list (make-let vars vals new-body))))  ; 组件序列

;(let ((var1 val1) (var2 val2) ...) body)
(define (make-let vars vals body)
  (cons 'let (cons (map list vars vals) body)))
; 首先(map list vars vals)组成的是((u '*unassigned*)这步，是组成序列，然后跟body组成序对，然后在跟'let组成序对

; 对环境的操作
; 阵对环境的基本操作
; 环境表示为一个框架的表,一个环境的外围环境就是这个表的cdr,空环境则直接用空表表示。
(define (enclosing-environment env) (cdr env))  ; 外围环境
(define (first-frame env) (car env))            ; 这个环境的第一个框架。
(define the-empty-environment '())              ; 空环境。
; 在环境里的每个框架一对表形成的序对，
; 一个是这个框架种所有元素的表，另一个是它们的约束值的表，也就是变量名和相应的变量值在两个表啦。
(define (make-frame variables values) ; 框架的构造函数
  (cons variables values))            ; 其实就是连接两个表，一个是变量名，一个是变量值。
(define (frame-variables frame) (car frame))   ; 取得变量名
(define (frame-values frame) (cdr frame))      ; 取得变量值
(define (add-binding-to-frame! var val frame)  ; 添加新值
  (set-car! frame (cons var (car frame)))      ; 就是在外边再包裹一层，然后修改地址。
  (set-cdr! frame (cons val (cdr frame))))     ; 同理。

; 返回符号在环境env里的约束值，
; 先扫描第一个框架里的变量名，如果找到了就返回
; 如果没找到就到外围环境中去找。
; 如果遇到空环境，就发出错误信号。
(define (lookup-variable-value var env)
  (define (env-loop env)         ; 定义一个内部函数
    (define (scan vars vals)     ; 内部函数,扫描
      (cond ((null? vars)        ; 如果找到最后也没找到
             (env-loop (enclosing-environment env))) ; 这里递归调用，从外围环境中继续找。
            ((eq? var (car vars)) (car vals))        ; 这里表示找到了
            (else (scan (cdr vars) (cdr vals)))))    ; 一个框架里可能有很多个变量名，这个是继续递归余下的。
    (if (eq? env the-empty-environment)      ; 如果环境为空，
        (error "Unbound variable" var)       ; 这里表示已经找到最顶层,但没找到
        (let ((frame (first-frame env)))     ; 首先在第一个环境中去找。
          (scan (frame-variables frame)      ; 两个参数，一个变量名
                (frame-values frame)))))     ; 一个变量值。
  (let ((val (env-loop env)))  ; 这里找到变量值了。     
    (if (unassigned? val)      ; 判断这个值是否为未定义的。
        (error "Unassigned variable" var)
        val)
    )

  )

; 返回一个新环境，这个环境包含了一个新的框架，所有位域vars中的元素约束到表vals里对应的元素，而其外围环境是base-env
(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))           ; 首先检查名称和值的个数是否相等。
      (cons (make-frame vars vals) base-env)    ; 组件一个框架
      (if (< (length vars) (length vals))       ; 不相等，就2种情况啦。
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))
;在环境env里的第一个框架加入一个新约束，它关联其变量var和值val
(define (define-variable! var val env)
  (let ((frame (first-frame env)))   ; 第一个框架
    (define (scan vars vals)         ; 这个扫描是扫描是否已有这个变量名，
      (cond ((null? vars)            ; 判断是否扫描到最后了                  
             (add-binding-to-frame! var val frame))    ; 这里表示没有，然后就新建啦。
            ((eq? var (car vars)) (set-car! vals val)) ; 这里表示已经有了，修改值啦
            (else (scan (cdr vars) (cdr vals)))))      ; 递归处理余下的。
    (scan (frame-variables frame) (frame-values frame))))

; 修改变量在环境里的约束。
(define (set-variable-value! var val env)     ; 参数依次为变量名,变量值,环境。
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)                                ; 判断是否到最后
             (env-loop (enclosing-environment env)))     ; 这层找完了，递归处理上一层。
            ((eq? var (car vars)) (set-car! vals val))   ; 如果找到了,就修改成新的值。
            (else (scan (cdr vars) (cdr vals)))))        ; 递归处理余下的
    (if (eq? env the-empty-environment)         ; 首先判断是否有环境吧。
        (error "Unbound variable: SET!" var)    ; 环境为空返回这个。
        (let ((frame (first-frame env)))        ; 第一个框架
          (scan (frame-variables frame)         ; 变量名
                (frame-values frame)))))        ; 
  (env-loop env))


; 一个基本过程对象表
(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
       ; ⟨more primitives⟩
        ))
; 取得基本过程名称
(define (primitive-procedure-names)
  (map car primitive-procedures))
; 取得基本过程的实现，前面加 'primitive ，以便eval识别。
(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))  ; 基本过程以'primitive开头啦。
       primitive-procedures))

(define (setup-environment)
  (let ((initial-env      ; 初始环境
         (extend-environment (primitive-procedure-names)   ; 变量名
                             (primitive-procedure-objects) ; 变量值
                             the-empty-environment)))      ; 上一层环境是空环境啦。
    (define-variable! 'true true initial-env)    ; 添加新约束
    (define-variable! 'false false initial-env)
    initial-env))  ; 返回构造的初始环境。
(define the-global-environment (setup-environment))     ; 初始环境为全局环境。

(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")
; 模拟读入、求值、打印的循环。
(define (driver-loop)
  (prompt-for-input input-prompt)                       ; 输入前缀
  (let ((input (read)))                                 ; 输入
    (let ((output (eval input the-global-environment))) ; 求值
      (announce-output output-prompt)                   ; 打印前缀
      (user-print output)))                             ; 打印输出。
  (driver-loop))

(define (prompt-for-input string)  ; 输入字符串。
  (newline) (newline) (display string) (newline))
(define (announce-output string)   ; 打印字符串。
  (newline) (display string) (newline))

; 打印
(define (user-print object)
  (if (compound-procedure? object)                  ; 首先判断是否为复合过程。
      (display (list 'compound-procedure            ; 复合过程标志头
                     (procedure-parameters object)  ; 参数
                     (procedure-body object)        ; 函数体
                     '<procedure-env>))             ; 这个是环境。
      (display object)))


(define apply-in-underlying-scheme apply)



; 这里开始执行吧。
;(driver-loop)

; 这里做的内核支持一次语法扫描,多次执行。
; 我们将句法分析和执行分离。


(driver-loop)