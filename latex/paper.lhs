\documentclass[9pt]{entcs}
\usepackage{prentcsmacro}
\usepackage{graphicx}
\usepackage{amssymb,amsmath}
\usepackage{semantic}
\usepackage{stackengine}
\usepackage{multicol}

\input{macros}

\sloppy
% The following is enclosed to allow easy detection of differences in
% ascii coding.
% Upper-case    A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
% Lower-case    a b c d e f g h i j k l m n o p q r s t u v w x y z
% Digits        0 1 2 3 4 5 6 7 8 9
% Exclamation   !           Double quote "          Hash (number) #
% Dollar        $           Percent      %          Ampersand     &
% Acute accent  '           Left paren   (          Right paren   )
% Asterisk      *           Plus         +          Comma         ,
% Minus         -           Point        .          Solidus       /
% Colon         :           Semicolon    ;          Less than     <
% Equals        =3D           Greater than >          Question mark ?
% At            @           Left bracket [          Backslash     \
% Right bracket ]           Circumflex   ^          Underscore    _
% Grave accent  `           Left brace   {          Vertical bar  |
% Right brace   }           Tilde        ~

% A couple of exemplary definitions:

\newcommand{\Nat}{{\mathbb N}}
\newcommand{\Real}{{\mathbb R}}
\def\lastname{Feitosa, Ribeiro, and Du Bois}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                        Begin of lts2TeX stuff                              %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.5,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor[rgb]{0.8,0.33,0.0}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0.06,0.06,0.06}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\pinkFG}[1]{\textcolor[rgb]{1.0,0.0,0.5}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
  \newcommand{\pink}{\pinkFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
  \newcommand{\pink}{\blackFG}
}

\ColourStuff

\newcommand{\K}[1]{\yellow{\mathsf{#1}}}
\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\Con}[1]{\green{\mathsf{#1}}}
\newcommand{\F}[1]{\blue{\mathsf{#1}}}
\newcommand{\V}[1]{\black{\mathsf{#1}}}
\newcommand{\N}[1]{\red{\mathsf{#1}}}
\newcommand{\JK}[1]{\purple{\mathsf{#1}}}
\newcommand{\RF}[1]{\pink{\mathsf{#1}}}
\newcommand{\Comm}[1]{\red{\textnormal{#1}}}

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\N{" a "}"
%subst comment a = "\footnotesize{\Comm{~\textit{-}\textit{-}~\textit{" a "}}}"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                          End of lhs2Tex stuff                              %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{frontmatter}
  \title{Towards an Extrinsic Formalization of Featherweight Java in Agda}
  \author{Samuel da Silva Feitosa\thanksref{email1}}
  \address{Departamento de Inform\'{a}tica\\Instituto Federal de Santa Catarina\\Ca\c{c}ador - SC, Brazil}
  \author{Rodrigo Geraldo Ribeiro\thanksref{email2}}
  \address{Programa de P\'{o}s-Gradua\c{c}\~{a}o em Ci\^{e}ncia da Computa\c{c}\~{a}o\\Universidade Federal de Ouro Preto\\Ouro Preto - MG, Brazil}
  \author{Andre Rauber Du Bois\thanksref{email3}}
  \address{Programa de P\'{o}s-Gradua\c{c}\~{a}o em Computa\c{c}\~{a}o\\Universidade Federal Pelotas\\Pelotas - RS, Brazil}
  \thanks[email1]{Email: {\texttt{\normalshape samuel.feitosa [at] ifsc.edu.br}}}
  \thanks[email2]{Email: {\texttt{\normalshape rodrigo.ribeiro [at] ufop.edu.br}}}
  \thanks[email3]{Email: {\texttt{\normalshape dubois [at] inf.ufpel.edu.br}}}
  
\begin{abstract} 
  Featherweight Java is one of the most popular calculi which specify object-oriented programming features. It has been used as the basis for investigating novel language functionalities, as well as to specify and understand the formal properties of existing features for languages in this paradigm. However, when considering mechanized formalization, it is hard to find an implementation for languages with complex structures and binding mechanisms as Featherweight Java. In this paper we formalize Featherweight Java, implementing the static and dynamic semantics in Agda, and proving the main safety properties for this calculus.
\end{abstract}

\begin{keyword}
Featherweight Java, Mechanized Semantics, Type Safety
\end{keyword}

\end{frontmatter}
\section{Introduction}\label{intro}

Currently, Java is one of the most popular programming languages \cite{tiobe2019}. It is a general-purpose, concurrent, strongly typed, class-based object-oriented language. Since its release in 1995 by Sun Microsystems, and later acquisition by Oracle, Java has been evolving over time, adding features and programming facilities in its new versions. For example, in a recent major release of Java, new features such as lambda expressions, method references, and functional interfaces, were added to the core language, offering a programming model that fuses the object-oriented and functional styles~\cite{gosling2014java}. 

Since a programming language evolves, it is important to have mechanisms to ensure that certain behavior and desired properties are maintained after changing the language's structure and the compiler or interpreter implementation. One way to do that is to formalize the language (or subset of it) in a proof assistant, such as Agda, Coq, or Isabelle, providing formal proofs of the desired properties. Although mechanized proof assistants are powerful tools, proof development can be difficult and time-consuming~\cite{Delaware:2011:PLT:2076021.2048113}. 

%There are two main approaches to formalize the static semantics of a programming language. In the first and more common approach, sometimes referred as \emph{extrinsic}, we start by defining the syntax of all elements of the programming language, and then a separate definition of typing judgments over the terms is provided. In the second, called \emph{inherently-typed} (or \emph{intrinsically-typed}), the syntax and the type judgments are expressed in a single definition which captures only well-typed expressions~\cite{Altenkirch:1999:MPL:647849.737066,Augustsson99anexercise,Reynolds01whatdo,BachPoulsen:2017:IDI:3177123.3158104}. Necessary lemmas and proofs of the first approach can be obtained (almost) for free by the host language type system when using an inherently-typed encoding. 

In this context, this paper discusses the steps to formalize Featherweight Java (FJ)~\cite{Igarashi:2001:FJM:503502.503505} in Agda, a dependently-typed functional programming language based on Martin-L\"of intuitionistic type theory~\cite{Lof98}. FJ is a small core calculus with a rigorous semantic definition of the main core aspects of Java. The motivations for using the specification of FJ are that it is very compact, and its minimal syntax, typing rules, and operational semantics fit well for modeling and proving properties for the compiler and programs. We adopt the most used method for proving safety of a programming language: the syntactic approach (sometimes called extrinsic) proposed by Wright and Felleisen~\cite{Wright:1994:SAT:191905.191909}. Using this technique, we define first the syntax, and then relations to express both the typing judgments (static semantics), and the evaluation through reduction steps (dynamic semantics). We prove the common theorems of \emph{progress} and \emph{preservation} to link the static and dynamic semantics, guaranteeing that a well-typed term will not get stuck, i.e., it should be a value or be able to take another reduction step, preserving the intended type. As far as we know, this is the first attempt to formalize an extrinsic version of FJ in Agda. Filling this gap, we provide to the interested reader the source-code which can be used to better understanding the approach and Agda, as well as to be extended for future developments.

More concretely, we make the following contributions:

\begin{itemize}
\item We specify the the static and dynamic semantics of FJ (class table and expressions) in Agda using the syntactic approach~\cite{Wright:1994:SAT:191905.191909}.
\item We prove that the specification is sound, i.e., we can show that the proposed theorems of \emph{progress} and \emph{preservation} hold.
\item We define a function to evaluate well-typed terms, by repeating the application of the \emph{progress} and \emph{preservation} proofs~\cite{Wadler-plfa}.
\end{itemize}

The remainder of this text is organized as follows: Section \ref{sec:fj} summarizes the FJ proposal.
% Section \ref{sec:dt} introduces the use of dependent types for defining inherently-typed syntax.
Section \ref{sec:mec} shows how we represent types, how we model the class table and expressions, and the specification of the static and dynamic semantics of FJ in Agda. Section \ref{sec:proofs} discusses the proof steps to guarantee type safety of the studied calculus. Section \ref{sec:eval} present the steps to define evaluation through repeated applications of the \emph{progress} and \emph{preservation} theorems. Section \ref{sec:rel} discusses related work. Finally, we present the final remarks in Section~\ref{sec:conclusion}.

All source-code presented in this paper has been formalized in Agda version 2.6.0 using Standard Library 1.0. We present here parts of the Agda code used in our definitions, not necessarily in a strict lexically-scoped order. Some formal proofs were omitted from the text for space reasons, and also to not distract the reader from understanding the high-level structure of the formalization. In such situations we give just proof sketches and point out where all details can be found in the source code. All source code produced, including the \LaTeX \ source of this paper, are available on-line~\cite{repos}.

\section{Featherweight Java: a Refresher}
\label{sec:fj}

Featherweight Java (FJ)~\cite{Igarashi:2001:FJM:503502.503505} is a minimal core calculus for Java, in the sense that as many features of Java as possible are omitted, while maintaining the essential flavor of the language and its type system. FJ is to Java what $\lambda$-calculus is to Haskell. It offers similar operations, providing classes, methods, attributes, inheritance and dynamic casts with semantics close to Java's. The Featherweight Java project favors simplicity over expressivity and offers only five ways to create terms: object creation, method invocation, attribute access, casting and variables~\cite{Igarashi:2001:FJM:503502.503505}. This fragment is large enough to include many useful programs.

%format JClA = "\Con{A}"
%format JClB = "\Con{B}"
%format JClPair = "\Con{Pair}"
%format JClObj = "\Con{Object}"
%format JCA = "\D{A}"
%format JCB = "\D{B}"
%format JCPair = "\D{Pair}"
%format setfst = "\D{setfst}"
%format class = "\JK{class}"
%format extends = "\JK{extends}"
%format super = "\JK{super}"
%format this = "\JK{this}"
%format new = "\JK{new}"
%format return = "\JK{return}"
%format this.fst=fst = "\JK{this}\V{.fst=fst}"
%format this.snd=snd = "\JK{this}\V{.snd=snd}"
%format this.snd = "\JK{this}\V{.snd}"
%format , = "\V{,}"

A program in FJ consists of the declaration of a set of classes and an expression to be evaluated, which corresponds to Java's main method. The following example shows how classes can be modeled in FJ. There are three classes, |JClA|, |JClB|, and |JClPair|, with constructor and method declarations.

\begin{spec}
class JClA extends JClObj {
  JCA() { super(); }
}
class JClB extends JClObj {
  JCB() { super(); }
}
class JClPair extends JClObj {
  JClObj fst; 
  JClObj snd;
  JCPair(JClObj fst, JClObj snd) {
    super(); 
    this.fst=fst;
    this.snd=snd;
  }
  JClPair setfst(JClObj newfst) {
    return new JClPair(newfst, this.snd);
  }
}
\end{spec}

In the following example we can see two different kinds of expressions: |new JClA|(), |new JClB|(), and |new JClPair|(...) are \emph{object constructors}, and .|setfst|(...) refers to a \emph{method invocation}:

\begin{spec}
new JClPair(new JClA(), new JClB()) . setfst(new JClB());
\end{spec}

FJ semantics provides a purely functional view without side effects. In other words, attributes in memory are not affected by object operations~\cite{Pierce:2002:TPL:509043}. Furthermore, interfaces, overloading, call to base class methods, null pointers, base types, abstract methods, statements, access control, and exceptions are not present in the language~\cite{Igarashi:2001:FJM:503502.503505}. As the language does not allow side effects, it is possible to formalize the evaluation directly on FJ terms, without the need for auxiliary mechanisms to model the heap~\cite{Pierce:2002:TPL:509043}. 

\subsection{Syntax and Auxiliary Functions}

The abstract syntax of FJ is given in Figure \ref{fig:fj-syntax}, where \texttt{L} represents classes, \texttt{K} defines constructors, \texttt{M} stands for methods, and \texttt{e} refers to the possible expressions. The metavariables \texttt{A}, \texttt{B}, \texttt{C}, \texttt{D}, and \texttt{E} can be used to represent class names, \texttt{f} and \texttt{g} range over field names, \texttt{m} ranges over method names, \texttt{x} and \texttt{y} range over variables, \texttt{d} and \texttt{e} range over expressions. Throughout this paper, we write $\overline{C}$ as shorthand for a possibly empty sequence $C_1,...,C_n$ (similarly for $\overline{f}$, $\overline{x}$, etc.). An empty sequence is denoted by $\bullet$, and the length of a sequence \texttt{\={x}} is written \texttt{\#\={x}}. We use $\Gamma$ to represent an environment, which is a finite mapping from variables to types, written $\overline{x} : \overline{T}$, and we let $\Gamma$(x) denote the type C such that x: C $\in \Gamma$. We slightly abuse notation by using set operators on sequences. Their meaning is as usual.

\begin{figure}[!htb]
	\begin{display}[.4]{Syntax}
		\category{L}{class declarations}\\
		\entry{\textrm{class $C$ extends} \ \{ \overline{C} \ \overline{f}; K \ \overline{M} \}}{}\\
		\category{K}{constructor declarations}\\
		\entry{C(\overline{C} \ \overline{f}) \ \{ \textrm{super}(\overline{f}); \ \textrm{this}.\overline{f}=\overline{f}; \}}{}\\
		\category{M}{method declarations}\\
		\entry{C \ \textrm{m}(\overline{C} \ \overline{x}) \ \{ \ \textrm{return} \ e; \}}{}\\
		\category{e}{expressions}\\
		\entry{x}{variable}\\
		\entry{e.f}{field access}\\
		\entry{e.\textrm{m}(\overline{e})}{method invocation}\\
		\entry{\textrm{new} \ C(\overline{e})}{object creation}\\
		\entry{(C) \ e}{cast}\\
	\end{display}
	\caption{Syntactic definitions for FJ.}
	\label{fig:fj-syntax}
\end{figure}


A class table \emph{CT} is a mapping from class names, to class declarations $L$, and it should satisfy some conditions, such as each class \texttt{C} should be in \emph{CT}, except \texttt{Object}, which is a special class; and there are no cycles in the subtyping relation. Thereby, a program is a pair $(CT, e)$ of a class table and an expression. 

Figure~\ref{fig:fj-subtyping} shows the rules for subtyping, where we write $C$ \texttt{<:} $D$ when $C$ is a subtype of $D$.

\begin{figure}[!htb]
	\[
	\begin{array}{c} 
	\textrm{$C <: C$}
	\\ \\
	
	\inference{\textrm{$C <: D$ \ \ \ \ \ $D <: E$}}
	{\textrm{$C <: E$}}
	\\ \\
	
	\inference{\textrm{CT($C$) = class $C$ extends $D$ \{ ... \} }}
	{\textrm{$C <: D$}}
	\end{array}
	\]
	\caption{Subtyping relation between classes.}
	\label{fig:fj-subtyping}
\end{figure}

The authors also proposed some auxiliary definitions for working in the typing and reduction rules. These definition are given in Figure~\ref{fig:fj-aux}. The rules for \emph{field lookup} demonstrate how to obtain the fields of a given class. If the class is \texttt{Object}, an empty list is returned. Otherwise, it returns a sequence $\overline{C}~\overline{f}$ pairing the type of each field with its name, for all fields declared in the given class and all of its superclasses. The rules for \emph{method type lookup} (\emph{mtype}) show how the type of method $m$ in class $C$ can be obtained. The first rule of \emph{mtype} returns a pair, written $\overline{B} -> B$, of a sequence of argument types $\overline{B}$ and a result type $B$, when the method $m$ is contained in $C$. Otherwise, it returns the result of a call to \emph{mtype} with the superclass. A similar approach is used in the rules for \emph{method body lookup}, where \emph{mbody}(m, $C$) returns a pair $(\overline{x},e)$, of a sequence of parameters $\overline{x}$ and an expression $e$. Both \emph{mtype} and \emph{mbody} are partial functions.

\vspace{5pt}

\begin{figure}[!htb]
\hspace{100pt} \textbf{Field lookup}
\[
\begin{array}{c} 
\textrm{\emph{fields}(Object) = $\bullet$} 
\vspace{4pt}
\end{array}
\]
\[
\begin{array}{c} 
\inference{\textrm{\emph{CT}($C$) = class~$C$~extends~$D$~\{$\overline{C}$~$\overline{f}$;~$K$~$\overline{M}$\}} \\
	\textrm{\emph{fields}($D$) = $\overline{D}$~$\overline{g}$}}
{\textrm{\emph{fields}($C$) = $\overline{D}$~$\overline{g}$, $\overline{C}$~$\overline{f}$}}
\vspace{4pt}
\end{array}
\]
\hspace{100pt} \textbf{Method type lookup}
\[
\begin{array}{c} 
\inference{\textrm{\emph{CT}($C$) = class~$C$~extends~$D$~\{$\overline{C}$~$\overline{f}$;~$K$~$\overline{M}$\}} \\
           \textrm{$B$ m($\overline{B}$ $\overline{x}$) \{ return $e$; \} $\in$ $\overline{M}$}}
{\textrm{\emph{mtype}(m, $C$) = $\overline{B}$ $->$ $B$}}
\end{array}
\vspace{4pt}
\]
\[
\begin{array}{c} 
\inference{\textrm{\emph{CT}($C$) = class~$C$~extends~$D$~\{$\overline{C}$~$\overline{f}$;~$K$~$\overline{M}$\} \ \ \ \ m $\notin$ $\overline{M}$}}
{\textrm{\emph{mtype}(m, $C$) = \emph{mtype}(m, $D$)}}
\end{array}
\vspace{4pt}
\]
\hspace{100pt} \textbf{Method body lookup}
\[
\begin{array}{c} 
\inference{\textrm{\emph{CT}($C$) = class~$C$~extends~$D$~\{$\overline{C}$~$\overline{f}$;~$K$~$\overline{M}$\}} \\
           \textrm{$B$ m($\overline{B}$ $\overline{x}$) \{ return $e$; \} $\in$ $\overline{M}$}}
{\textrm{\emph{mbody}(m, $C$) = ($\overline{x}$, $e$)}}
\end{array}
\vspace{4pt}
\]
\[
\begin{array}{c} 
\inference{\textrm{\emph{CT}($C$) = class~$C$~extends~$D$~\{$\overline{C}$~$\overline{f}$;~$K$~$\overline{M}$\} \ \ \ \ m $\notin$ $\overline{M}$}}
{\textrm{\emph{mbody}(m, $C$) = \emph{mbody}(m, $D$)}}
\end{array}
\vspace{4pt}
\]
\caption{Auxiliary definitions.}
\label{fig:fj-aux}
\end{figure}

\subsection{Typing and Reduction Rules}

This section presents how the typing rules of FJ are used to guarantee type soundness, i.e., well-typed terms do not get stuck, and the reduction rules showing how each step of evaluation should be processed for FJ syntax. Figure~\ref{fig:semantics} shows in the left side, the typing rules for expressions, and in the right side, it shows first the rules to check if methods and classes are well-formed, then the reduction rules for this calculus. We omit here the congruence rules, which can be found in the original paper~\cite{Igarashi:2001:FJM:503502.503505}.

The typing judgment for expressions has the form $\Gamma \vdash$ \texttt{e: C}, meaning that in the environment $\Gamma$, expression \texttt{e} has type \texttt{C}. The abbreviations when dealing with sequences is similar to the previous section. The typing rules are syntax directed, with one rule for each form of expression, save that there are three rules for casts. 

\begin{figure*}[!htb]
\begin{multicols}{2}
\hspace{-2ex} \textbf{Expression typing}
\[
\hspace{-6ex}
\begin{array}{c} 
\inference{}
          {\textrm{$\Gamma \vdash$ x: $\Gamma$(x)}}[{[T-Var]}]
\\ \\

\inference{\textrm{$\Gamma \vdash$ e$_0$: C$_0$ \ \ \ \ \emph{fields}(C$_0$) = \={C} \={f}}}
          {\textrm{$\Gamma \vdash$ e$_0$.f$_i$: C$_i$}}[{[T-Field]}]
\\ \\

\inference{\textrm{\emph{mtype}(m, C$_0$) = \={D} $->$ C} \\
           \textrm{$\Gamma \vdash$ e$_0$ : C$_0$ \ \ \ \ $\Gamma \vdash$ \={e} : \={C} \ \ \ \ \={C} $<$: \={D}}}
          {\textrm{$\Gamma \vdash$ e$_0$.m(\={e}) : C}}[{[T-Invk]}]
\\ \\

\inference{\textrm{\emph{fields}(C) = \={D} \={f}} \\
           \textrm{$\Gamma \vdash$ \={e} : \={C} \ \ \ \ \={C} $<$: \={D}}}
          {\textrm{$\Gamma \vdash$ new C(\={e}) : C}}[{[T-New]}]
\\ \\

\inference{\textrm{$\Gamma \vdash$ e$_0$ : D \ \ \ \ D $<$: C}}
          {\textrm{$\Gamma \vdash$ (C) e$_0$ : C}}[{[T-UCast]}]
\\ \\

\inference{\textrm{$\Gamma \vdash$ e$_0$ : D \ \ \ \ C $<$: D \ \ \ \ C $\neq$ D}}
          {\textrm{$\Gamma \vdash$ (C) e$_0$ : C}}[{[T-DCast]}]
\\ \\

\inference{\textrm{$\Gamma \vdash$ e$_0$ : D \ \ \ \ C $\nless$: D \ \ \ \ D $\nless$: C}\\
           \textrm{\emph{stupid warning}}}
          {\textrm{$\Gamma \vdash$ (C) e$_0$ : C}}[{[T-SCast]}]
\vspace{5pt}
\end{array}
\]

\columnbreak
	
\hspace{-10ex} \textbf{Method typing}
\[
\hspace{-10ex}
\begin{array}{c} 
\inference{\textrm{\={x}: \={C}, this: C $\vdash$ e$_0$: E$_0$ \ \ \ \ E$_0$ \texttt{<:} C$_0$} \\
           \textrm{class C extends D \{...\}} \\
           \textrm{if \emph{mtype}(m, D) = \={D} $->$ D$_0$, then \={C} = \={D} and C$_0$ = D$_0$}}
          {\textrm{C$_0$ m(\={C} \={x}) \{ return e$_0$; \} OK in C}}
\end{array}
\]

\hspace{-10ex} \textbf{Class typing}
\[
\hspace{-10ex}
\begin{array}{c} 
\inference{\textrm{K = C(\={D} \={g}, \={C} \={f}) \{ super(\={g}); this.\={f} = \={f}; \}} \\
           \textrm{\emph{fields}(D) = \={D} \={g} \ \ \ \ \={M} OK in C}}
          {\textrm{class C extends D \{ \={C} \={f}; K \={M} \} OK}} 
\end{array}
\]

\hspace{-10ex} \textbf{Evaluation}
\[
\hspace{-12ex}
\begin{array}{c} 
\inference{\textrm{\emph{fields}(C) = \={C}~\={f}}}
          {\textrm{(new \emph{C}($\bar{v}$)).f$_i$ $-->$ v$_i$}}[{[R-Field]}]
\\ \\

\inference{\textrm{\emph{mbody}(m, C) = (\={x}, e$_0$)}}
          {\textrm{(new \emph{C}($\bar{v}$)).m(\={d}) $-->$ [\={d} $\mapsto$ \={x}, new C($\bar{v}$) $\mapsto$ this] e$_0$}}[{[R-Invk]}]
\\ \\

\inference{\textrm{C $<:$ D}}
          {\textrm{(D) (new C($\bar{v}$)) $-->$ new C($\bar{v}$)}}[{[R-Cast]}]
\end{array}
\]
\end{multicols}
\caption{Typing and evaluation rules.}
\label{fig:semantics}
\end{figure*}

The rule \texttt{T-Var} results in the type of a variable $x$ according to the context $\Gamma$. If the variable $x$ is not contained in $\Gamma$, the result is undefined. Similarly, the result is undefined when calling the functions \texttt{fields}, \texttt{mtype}, and \texttt{mbody} in cases when the target class or the methods do not exist in the given class. The rule \texttt{T-Field} applies the typing judgment on the subexpression \texttt{e$_0$}, which results in the type \texttt{C$_0$}. Then it obtains the \emph{fields} of class \texttt{C$_0$}, matching the position of \texttt{f$_i$} in the resultant list, to return the respective type \texttt{C$_i$}. The rule \texttt{T-Invk} also applies the typing judgment on the subexpression \texttt{e$_0$}, which results in the type \texttt{C$_0$}, then it uses \emph{mtype} to get the formal parameter types \texttt{\={D}} and the return type \texttt{C}. The formal parameter types are used to check if the actual parameters \texttt{\={e}} are subtypes of them, and in this case, resulting in the return type \texttt{C}. The rule \texttt{T-New} checks if the actual parameters are a subtype of the constructor formal parameters, which are obtained by using the function \emph{fields}. There are three rules for casts: one for \emph{upcasts}, where the subject is a subclass of the target; one for \emph{downcasts}, where the target is a subclass of the subject; and another for \emph{stupid casts}, where the target is unrelated to the subject. Even considering that Java's compiler rejects as ill-typed an expression containing a stupid cast, the authors found that a rule of this kind is necessary to formulate type soundness proofs.

The rule for \emph{method typing} checks if a method declaration \texttt{M} is well-formed when it occurs in a class \texttt{C}. It uses the expression typing judgment on the body of the method, with the context $\Gamma$ augmented with variables from the actual parameters with their declared types, and the special variable \texttt{this}, with type \texttt{C}. The rule for \emph{class typing} checks if a class is well-formed, by checking if the constructor applies super to the fields of the superclass and initializes the fields declared in this class, and that each method declaration in the class is well-formed.

There are only three computation rules, indicating which expressions can be used in the main program. The first rule \texttt{R-Field} formalizes how to evaluate an \emph{attribute access}. Similarly to the typing rule \texttt{T-Field}, it uses the function \emph{fields}, and matches the position $i$ of the field \texttt{f$_i$} in the resulting list, returning the value \texttt{v$_i$}, which refers to the value in the position $i$ of the actual parameter list. The second rule \texttt{R-Invk} shows the evaluation procedure for a \emph{method invocation}, where firstly it obtains the method body expression \texttt{m} of class \texttt{C} through the function \emph{mbody}, and then performs substitution of the actual parameters and the special variable \texttt{this} in the body expression, similar to a beta reduction on $\lambda$-calculus. The last rule \texttt{R-Cast} refers to \emph{cast processing}, where the same subexpression \texttt{new C(\={e})} is returned in case the subject class \texttt{C} is subtype of the target class \texttt{D}. There are also five congruence rules\footnote{The congruence rules omitted from the text can be found in p. 407 of \cite{Igarashi:2001:FJM:503502.503505}.} (omitted from Figure~\ref{fig:semantics}), which are responsible for the intermediary evaluation steps for the proposed small-step semantics.

The FJ calculus is intended to be a starting point for the study of various operational features of object-oriented programming in Java-like languages, being compact enough to make rigorous proofs feasible. Besides the rules for evaluation and type-checking,
Igarashi et al.~\cite{Igarashi:2001:FJM:503502.503505} present (paper) proofs of type soundness for FJ.

\section{Mechanization of Featherweight Java}
\label{sec:mec}

This section presents our formalization of a large subset of FJ using the usual syntactic (extrinsic) approach proposed by Wright and Felleisen~\cite{Wright:1994:SAT:191905.191909}. We use Agda, an advanced programming language based on Type Theory. Agda's type system is expressive enough to support full functional verification of programs~\cite{Stump:2016:VFP:2841316}, giving programmers the power to guarantee the absence of bugs, and thus improving the quality of software in general. By using such extrinsic approach, we first define a bunch of relations (inductive data types) to specify the syntax, auxiliary definitions, the behavior (reduction rules), and the type system of the FJ programming language. Once defined the complete set of rules, we write proofs of properties about them. The proofs are separate external artifacts, which use structural induction to verify the desired properties. In this case, we are interested in mechanically proving the properties defined on paper in the original FJ~\cite{Igarashi:2001:FJM:503502.503505}, which include several lemmas, and the properties of \emph{progress} and \emph{preservation}, which together provide guarantees of type safety.

%format String = "\D{String}"
%format Bool = "\D{Bool}"
%format Set = "\D{Set}"
%format List = "\D{List}"
%format forall = "\V{\forall}"
%format ℓ = "\V{\ell}"
%format ~Nr1~ = "\N{1}"
%format ~Nr2~ = "\N{2}"
%format _==_ = "\D{\_ \equiv \_}"
%format == = "\D{\equiv}"
%format refl = "\Con{refl}"
%format Fin   = "\D{Fin}"
%format lookup = "\F{lookup}"
%format not = "\F{\neg}"
%format Dec = "\D{Dec}"
%format yes = "\Con{yes}"
%format no  = "\Con{no}"
%format Even = "\Con{Even}"
%format Odd = "\Con{Odd}"
%format Parity = "\D{Parity}"
%format parity = "\F{parity}"
%format natToBin = "\F{natToBin}"
%format false = "\Con{false}"
%format true = "\Con{true}"
%format + = "\F{+}"
%format ++ = "\F{++}"
%format Bot = "\D{\bot}"
%format All = "\D{All}"
%format Expr = "\D{Expr}"
%format True = "\Con{True}"
%format False = "\Con{False}"
%format Num = "\Con{Num}"
%format _&_ = "\Con{\_\land\_}"
%format _+_ = "\Con{\_+\_}"
%format Ty = "\D{Ty}"
%format Natt = "\Con{Nat}"
%format Booll = "\Con{Bool}"
%format Var = "\Con{Var}"
%format Lam = "\Con{Lam}"
%format App = "\Con{App}"
%format Val = "\D{Val}"
%format V-True = "\Con{V\textrm{-}True}"
%format V-False = "\Con{V\textrm{-}False}"
%format V-Lam = "\Con{V\textrm{-}Lam}"
%format ∀ = "\V{\forall}"
%format → = "\rightarrow"
%format _⟶_ = "\D{\_\longrightarrow\_}"
%format ⟶ = "\D{\longrightarrow}"
%format R-App₁ = "\Con{R\textrm{-}App_1}"
%format R-App₂ = "\Con{R\textrm{-}App_2}"
%format R-App = "\Con{R\textrm{-}App}"
%format e = "\V{e}"
%format e' = "\V{e''}"
%format e₁ = "\V{e_1}"
%format e₂ = "\V{e_2}"
%format e₁' = "\V{e_1''}"
%format e₂' = "\V{e_2''}"
%format v₁ = "\V{v_1}"
%format subs = "\D{subs}"
%format subst = "\D{subst}"
%format bool = "\Con{bool}"
%format _⇒_ = "\Con{\_\Longrightarrow\_}"
%format ⇒ = "\Con{\Longrightarrow}"
%format T-True = "\Con{T\textrm{-}True}"
%format T-False = "\Con{T\textrm{-}False}"
%format T-Var = "\Con{T\textrm{-}Var}"
%format T-Lam = "\Con{T\textrm{-}Lam}"
%format T-App = "\Con{T\textrm{-}App}"
%format _⊢_∶_ = "\D{\_\vdash\_:\_}"
%format _∋_∶_ = "\D{\_\ni\_:\_}"
%format ⊢ = "\D{\vdash}"
%format ∶ = "\D{:}"
%format ∋ = "\D{\ni}"
%format Ctx = "\D{Ctx}"
%format Γ = "\V{\Gamma}"
%format τ = "\V{\tau}"
%format τ₁ = "\V{\tau_1}"
%format τ₂ = "\V{\tau_2}"
%format ℕ = "\D{\mathbb{N}}"
%format × = "\D{\times}"
%format preservation = "\D{preservation}"
%format r₁ = "\V{r_1}"
%format r₂ = "\V{r_2}"
%format progress = "\D{progress}"
%format canonical = "\D{canonical}"
%format Progress = "\D{Progress}"
%format Canonical = "\D{Canonical}"
%format Done = "\Con{Done}"
%format Step = "\Con{Step}"
%format C-Lam = "\Con{C\textrm{-}Lam}"
%format C-True = "\Con{C\textrm{-}True}"
%format C-False = "\Con{C\textrm{-}False}"
%format σ = "\V{\sigma}"
%format ∷ = "\Con{::}"
%format _∈_ = "\D{\_\in\_}"
%format ∈ = "\D{\in}"
%format Value = "\D{Value}"
%format Env = "\D{Env}"
%format record = "\K{record}"
%format field = "\K{field}"
%format Class = "\D{Class}"
%format Meth = "\D{Meth}"
%format Name = "\D{Name}"
%format Field = "\Con{Field}"
%format Invk = "\Con{Invk}"
%format New = "\Con{New}"
%format cname = "\RF{cname}"
%format super = "\RF{super}"
%format ext = "\RF{ext}"
%format flds = "\RF{flds}"
%format meths = "\RF{meths}"
%format ret = "\RF{ret}"
%format params = "\RF{params}"
%format body = "\RF{body}"

\subsection{Syntax}

The syntax of FJ includes the definition of a class table (CT), which stores all classes in a source-code program, and an expression, which replaces the Java's main method. An expression can refer to information of two sources: (1) a context to deal with variables, which stores the actual parameters during a method invocation; (2) the class table, to perform operations involving attributes or methods. Besides, there is a mutual relation between classes and expressions: an expression can refer to information about classes, and a class can contain expressions (which represent the method body).

Considering all this, we start our formalization in Agda by defining the syntactic elements regarding FJ. A |Class| is represented by a record with four fields. The class name is stored in |cname|, the base class is in |super|, the attributes are in |flds|, and the methods are in |meths|. We keep all names abstract, and the only requirement for them is equality. For simplicity, we define |Name = ℕ|, a simple type which satisfies this requirement.

\begin{spec}
record Class : Set where
  field
    cname  : Name
    super  : Name
    flds   : List (Name × Name)
    meths  : List (Name × Meth)
\end{spec}

As we can see, attributes are represented by a |List| of tuples |(Name × Name)|, encoding the name and the type for each field. For methods, we have a similar setting, however, we use a |List| of tuples |(Name × Meth)|, where the first element is the method name, and the second encodes the method information, containing the return type |ret|, the method parameters |params|, and the method body |body|, as we can see next.

\begin{spec}
record Meth : Set where
  field
    ret     : Name
    params  : List (Name × Name)
    body    : Expr
\end{spec}

As we mentioned before, an expression can appear in two parts of a FJ program. It can appear in a method body, or it can represent the Java's main method, acting as a starting point for the program. We represent it using an inductive definition, considering the following constructors.

\begin{spec}
data Expr : Set where
  Var    : Name → Expr
  Field  : Expr → Name → Expr
  Invk   : Expr → Name → List Expr → Expr
  New    : Name → List Expr → Expr
\end{spec}

A variable is represented by the constructor |Var|, which receives a variable name as argument. A field access is encoded by |Field|, receiving two arguments. The first is an |Expr| which represents the instantiated object, and the second is the attribute name. A method invocation is encoded by |Invk| and receives three arguments. The first is similar to |Field|, the second is the method name, and the third is the formal parameters on a method invocation. Lastly, an object instantiation is defined by |New|, receiving two arguments. The first is the class name being instantiated, and the second is a list of formal parameters for the constructor. The complete BNF grammar is presented in~\cite{Igarashi:2001:FJM:503502.503505}.

The only possible value in FJ is encoded in the |Val| definition. 

%format V-New = "\Con{V\textrm{-}New}"

\begin{spec}
data Val : Expr → Set where
  V-New : ∀ {c cp} → All Val cp → Val (New c cp)
\end{spec}

Since Java adopts a call-by-value evaluation strategy, to be a value, we need an object instantiation with all parameters being values themselves. This was encoded using the Agda's standard library's datatype |All|, which associates the predicate |Val| for each element of the given list |cp|.

%format fields = "\D{fields}"
%format method = "\D{method}"
%format Obj = "\D{Obj}"
%format ct = "\D{ct}"
%format Δ = "\V{\Delta}"
%format obj = "\Con{obj}"
%format other = "\Con{other}"
%format this = "\Con{this}"
%format Class.flds = "\RF{Class.flds}"
%format Class.super = "\RF{Class.super}"
%format Class.meths = "\RF{Class.meths}"

\subsection{Auxiliary definitions}

A FJ expression can refer to information present on the class table, where all classes of a given program are stored. To reason about information of a given class, we defined two auxiliary definitions. Using the definition |fields| one can refer to information about the attributes of a class, including the fields inherited by its |super| class.

\begin{spec}
data fields : Name → List (Name × Name) → Set where
  obj    : fields Obj []
  other  : ∀ {c cd sf}
         → Δ ∋ c ∶ cd
         → fields (Class.super cd) sf
         → fields c (sf ++ Class.flds cd)
\end{spec}

We use an auxiliary definition (|_∋_∶_|)\footnote{We omit the code of |_∋_∶_| predicate, but it can be found in our repository~\cite{repos}.} which binds a value |cd| (class definition) from an element |c| (class name) in a list of pairs |Δ| (class table). In our encoding, we use this definition several times to lookup information about classes, fields, methods, and variables.

By using the predicate |method| it is possible to refer information about a specific method in a certain class. 

\begin{spec}
data method : Name → Name → Meth → Set where
  this : ∀ {c cd m mdecl}
       → Δ ∋ c ∶ cd
       → (Class.meths cd) ∋ m ∶ mdecl
       → method c m mdecl 
\end{spec}

Both auxiliary definitions refer to information on a class table |Δ|, which is defined globally in the working module.

%format R-Field = "\Con{R\textrm{-}Field}"
%format RC-Field = "\Con{RC\textrm{-}Field}"
%format R-Invk = "\Con{R\textrm{-}Invk}"
%format RC-InvkRecv = "\Con{RC\textrm{-}InvkRecv}"
%format RC-InvkArg = "\Con{RC\textrm{-}InvkArg}"
%format RC-NewArg = "\Con{RC\textrm{-}NewArg}"
%format flds = "\V{flds}"
%format interl = "\D{interl}"
%format Meth.params = "\RF{Meth.params}"
%format Meth.body = "\RF{Meth.body}"
%format ↦ = "\D{\longmapsto}"

\subsection{Reduction rules}

The reduction predicate takes two expressions as arguments. The predicate holds when expression |e| reduces to some expression |e'|. The evaluation relation is defined with the following type.

\begin{spec}
data _⟶_ : Expr → Expr → Set 
\end{spec}

When encoding the reduction relation, we use two important definitions: |interl|, which is an inductive definition to interleave the information of a list of pairs (|List (Name × A)|) with a |List B|, providing a new list |List (Name × B)|; and |subs|, which is responsible to apply the substitution of a parameter list into a method body. We present only their types next\footnote{The details about both definitions can be found online~\cite{repos}.}.

\begin{spec}
data interl : List (Name × A) → List B → List (Name × B) → Set
-- Inductive definition code omitted.  
subs : Expr → List (Name × Expr) → Expr
-- Function code omitted.
\end{spec}

From now on we explain each constructor of the evaluation relation |_⟶_| separately to make it easier for the reader.

Constructor |R-Field| encodes the behavior when accessing a field of a given class. All fields of a class are obtained using |fields C flds|. We interleave the definition of fields |flds| with the list of expressions |cp| received as parameters for the object constructor by using |interl flds cp fes|. With this information, we use |fes ∋ f ∶ fi| to bind the expression |fi| related to field |f|.

\begin{spec}
  R-Field : ∀ {C cp flds f fi fes}
             → fields C flds
             → interl flds cp fes
             → fes ∋ f ∶ fi
             → Field (New C cp) f ⟶ fi
\end{spec}

Constructor |R-Invk| represents the encoding to reduce a method invocation. We use |method C m MD| to obtain the information about method |m| on class |C|. As in |R-Field| we interleave the information about the method parameters |Meth.params MD| with a list of expressions |ap| received as the actual parameters on the current method invocation. Then, we use the function |subs| to apply substitution of the parameters in the method body.

\begin{spec}
  R-Invk : ∀ {C cp m MD ap ep}
             → method C m MD
             → interl (Meth.params MD) ap ep
             → Invk (New C cp) m ap ⟶ subs (Meth.body MD) ep
\end{spec}

%format _↦_ = "\D{\_\longmapsto\_}"

All the next constructors represent the congruence rules of the FJ calculus. Reduction of the first expression |e| is done by |RC-Field| and |RC-InvkRecv|, producing an |e'|.

\begin{spec}
  RC-Field : ∀ {e e' f}
             → e ⟶ e'
             → Field e f ⟶ Field e' f
  RC-InvkRecv : ∀ {e e' m mp}
             → e ⟶ e'
             → Invk e m mp ⟶ Invk e' m mp
\end{spec}

Reduction of arguments when invoking a method or instantiating an object is done by |RC-InvkArg| and |RC-NewArg|.

\begin{spec}               
  RC-InvkArg : ∀ {e m mp mp'}
             → mp ↦ mp'
             → Invk e m mp ⟶ Invk e m mp'
  RC-NewArg : ∀ {C cp cp'}
             → cp ↦ cp'
             → New C cp ⟶ New C cp'
\end{spec}

We use an extra predicate |_↦_| (note the different arrow) to evaluate a list of expressions recursively. 

%format T-Field = "\Con{T\textrm{-}Field}"
%format T-Invk = "\Con{T\textrm{-}Invk}"
%format T-New = "\Con{T\textrm{-}New}"
%format Meth.ret = "\RF{Meth.ret}"
%format proj₁ = "\RF{proj_1}"
%format proj₂ = "\RF{proj_2}"
%format unzip = "\D{unzip}"
%format ⊧ = "\D{\models}"
%format _⊧_∶_ = "\D{\_\models\_:\_}"

\subsection{Typing rules}

The typing rules for FJ are divided in two main parts: there are two predicates to type an expression, and two predicates to check if classes and methods are well-formed. A FJ program is well-typed if all typing predicates hold for a given program.

To type an expression, we have the typing judgment predicate |_⊢_∶_| which encodes the typing rules of FJ, and the predicate |_⊧_∶_| responsible to apply the typing judgment |_⊢_∶_| to a list of expressions recursively. Their type definitions are shown below.

\begin{spec}
data _⊢_∶_  : Ctx → Expr → Name → Set
data _⊧_∶_  : Ctx → List Expr → List Name → Set  
\end{spec}

Both definitions are similar, receiving three parameters each. The first parameter is a type context |Ctx|, defined as a list of pairs |List (Name × Name)|, aiming to store the types for variables. The second is represented by an |Expr| for the typing judgment, and a |List Expr| for the recursive case, both representing the expressions being typed. The last argument is a |Name| (or |List Name|) representing the types for the given expressions. Next we present each constructor for the |_⊢_∶_| predicate.

The constructor |T-Var| uses the auxiliary definition |_∋_∶_| to lookup the context, binding the type |C| for a variable |x| in a context |Γ|.

\begin{spec}
  T-Var : ∀ {Γ x C}
         → Γ ∋ x ∶ C
         → Γ ⊢ (Var x) ∶ C
\end{spec}

Constructor |T-Field| is more elaborated. First, we use the typing judgment to obtain the type of the sub-expression |e|. Then, we use the auxiliary definition |fields| which gives us the attributes |flds| of a class |C|. Like variables, the type of |f| is obtained by the information stored in |flds|.

\begin{spec}
  T-Field : ∀ {Γ C Ci e f flds}
         → Γ ⊢ e ∶ C
         → fields C flds
         → flds ∋ f ∶ Ci
         → Γ ⊢ (Field e f) ∶ Ci
\end{spec}

Constructor |T-Invk| also uses the typing judgment to obtain the type for the sub-expression |e|. After that, we use our auxiliary predicate |method| to obtain the definition of method |m| in class |C|. It is used to type-check the method parameters |mp|\footnote{We use |proj₂| to get the second argument of a tuple, and |unzip| to split a list of tuples.}. Considering that all the premises hold, the type of a method invocation is given by |Meth.ret MD|.

\begin{spec}
  T-Invk : ∀ {Γ C e m MD mp}
         → Γ ⊢ e ∶ C
         → method C m MD
         → Γ ⊧ mp ∶ proj₂ (unzip (Meth.params MD))
         → Γ ⊢ (Invk e m mp) ∶ (Meth.ret MD)
\end{spec}

Similarly to |T-Invk|, in the definition |T-New| we also use the predicate to type a list of expressions. In this case, the premises will hold if the actual parameters |cp| of the class constructor are respecting the expected types for the |fields| of a given class |C|. 

\begin{spec}
  T-New : ∀ {Γ C cp flds}
         → fields C flds
         → Γ ⊧ cp ∶ proj₂ (unzip flds)
         → Γ ⊢ (New C cp) ∶ C
\end{spec}

%format ClassOk = "\D{ClassOk}"
%format MethodOk = "\D{MethodOk}"
%format T-Class = "\Con{T\textrm{-}Class}"
%format T-Method = "\Con{T\textrm{-}Method}"

%For space reasons, we omit the code definitions |ClassOk| and |MethodOk|, which specify the rules for typing classes and methods. These definitions can be fully seen in our source-code repository~\cite{repos}.

A class is well-formed if it respects the |ClassOk| predicate. In our definition, we use the |All| datatype to check if all methods are correctly typed.

\begin{spec}
data ClassOk : Class → Set where
  T-Class : ∀ {CD}
         → All (MethodOk CD) (proj₂ (unzip (Class.meths CD)))
         → ClassOk CD
\end{spec}

Similarly, a method is well-formed in a class if it respects the |MethodOk| predicate. We use the expression typing judgment as a premise to type-check the expression body using the formal parameters as the environment |Γ|, expecting the type defined as the return type of the given method.

\begin{spec}
data MethodOk : Class → Method → Set where
  T-Method : ∀ {CD MD}
          → Meth.params MD ⊢ Meth.body MD ∶ Meth.ret MD
          → MethodOk CD MD
\end{spec}

%format rewrite = "\K{rewrite}"
%format ⊢-interl = "\D{\vdash\hspace{-3pt}\textrm{-}interl}"
%format ⊧-interl = "\D{\models\hspace{-3pt}\textrm{-}interl}"
%format ∋-interl = "\D{\ni\hspace{-3pt}\textrm{-}interl}"
%format ⊢-method = "\D{\vdash\hspace{-3pt}\textrm{-}method}"
%format ≡-fields = "\D{\equiv\hspace{-3pt}\textrm{-}fields}"
%format ≡-method = "\D{\equiv\hspace{-3pt}\textrm{-}method}"
%format progress-list = "\D{progress\textrm{-}list}"
%format preservation-list = "\D{preservation\textrm{-}list}"
%format fs₁ = "\V{fs_1}"
%format fs₂ = "\V{fs_2}"
%format fs₃ = "\V{fs_3}"

\section{Proving Safety Properties}
\label{sec:proofs}

We proved type soundness through the standard theorems of \emph{preservation} and \emph{progress} for our formalization of FJ. This section presents only the main proofs, which use several lemmas to fulfill the proof requirements. The interested reader can refer to our source-code repository to see the intricacies of the whole proofs. 

The function |preservation| is the Agda encoding for the theorem with the same name, stating that if we have a well-typed expression, it preserves type after taking a reduction step. The proof proceeds by induction on the typing derivation of the first expression. 

\vspace{-2ex}

\begin{spec}
preservation : ∀ {e e' τ} → [] ⊢ e ∶ τ → e ⟶ e' → [] ⊢ e' ∶ τ
preservation (T-Var x) ()
preservation (T-Field tp fls bnd) (RC-Field ev) =
  T-Field (preservation tp ev) fls bnd
preservation (T-Field (T-New fs₁ tps) fs₂ bnd) (R-Field fs₃ zp bnde)
  rewrite ≡-fields fs₁ fs₂ | ≡-fields fs₂ fs₃ = ⊢-interl zp tps bnd bnde
preservation (T-Invk tp tmt tpl) (RC-InvkRecv ev) =
  T-Invk (preservation tp ev) tmt tpl
preservation (T-Invk tp tmt tpl) (RC-InvkArg evl) =
  T-Invk tp tmt (preservation-list tpl evl)
preservation (T-Invk (T-New fls cp) tmt tpl) (R-Invk rmt zp)
  rewrite ≡-method rmt tmt = subst (⊢-method tmt) tpl zp
preservation (T-New fls tpl) (RC-NewArg evl) =
  T-New fls (preservation-list tpl evl)
\end{spec}

\vspace{-2ex}

The case for constructor |T-Var| is impossible, because a variable term cannot take a step, and we finish this case using the Agda's absurd |()| pattern. Constructor |T-Field| has two cases: (1) the congruence rule, applying the induction hypothesis in the first expression; (2) the reduction step, where using the auxiliary lemmas |≡-fields| and |⊢-interl| we show that the expression |e'| preserves the initial type of expression |e|. The |T-Invk| constructor is the most intricate, with three cases: (1) the congruence rule for the first expression, where we apply the induction hypothesis; (2) the congruence for the list of arguments, where we use an auxiliary proof |preservation-list| which applies the induction hypothesis for each argument; (3) the reduction step, where we show that after a reduction step the type is preserved by using the auxiliary lemmas |≡-method|, |⊢-method|, and |subst|\footnote{These lemmas are omitted from this text, but can be found in our source code repository~\cite{repos}.}. The function |subst| represents the lemma which states that \emph{Expression substitution preserves typing}~\cite{Igarashi:2001:FJM:503502.503505}. Lastly, |T-New| has only the congruence case for which we apply the induction hypothesis for each argument of the class constructor.

Similarly to the previous theorem, the |progress| function represents the theorem with the same name, stating that if a well-typed expression |e| has type |τ| in an empty context |[]|, then it can make \emph{Progress}, i.e., or |e| is a value, or it can take another reduction step. We use the inductive datatype |Progress| to hold the result of our proof, with two constructors: |Done| when |e| is a value, and |Step| when |e| reduces to an |e'|.

\vspace{-2ex}

\begin{spec}
progress : ∀ {e τ} → [] ⊢ e ∶ τ → Progress e
progress (T-Var ())
progress (T-Field tp fls bnd) with progress tp
progress (T-Field tp fls bnd) | Step ev = Step (RC-Field ev)
progress (T-Field (T-New flds fts) fls bnd) | Done ev
  rewrite ≡-fields flds fls = Step (R-Field fls (proj₂ (⊧-interl fts))
    (proj₂ (∋-interl fts (proj₂ (⊧-interl fts)) bnd)))
progress (T-Invk tp mt tpl) with progress tp
progress (T-Invk tp mt tpl) | Step ev = Step (RC-InvkRecv ev)
progress (T-Invk tp mt tpl) | Done ev with progress-list tpl
progress (T-Invk tp mt tpl) | Done ev | Step evl =
  Step (RC-InvkArg evl) 
progress (T-Invk (T-New flds fts) mt tpl) | Done ev | Done evl =
  Step (R-Invk mt (proj₂ (⊧-interl tpl)))
progress (T-New fls tpl) with progress-list tpl
progress (T-New fls tpl) | Step evl = Step (RC-NewArg evl)
progress (T-New fls tpl) | Done evl = Done (V-New evl)
\end{spec}

Most cases are simple, and the reader should understand without further explanation. The complicated cases are those for |T-Field| and |T-Invk|, when processing the actual reduction step. When proving \emph{progress} for |T-Field|, to be able to produce a |R-Field| we needed to write two extra lemmas |⊧-interl| and |∋-interl|, which were omitted here for brevity. The case for |T-Invk| also used the lemma |⊧-interl| to produce a |R-Invk|. 

%format _↠_ = "\D{\_\twoheadrightarrow\_}"
%format ↠ = "\D{\twoheadrightarrow}"
%format eval = "\D{eval}"
%format Finished = "\D{Finished}"
%format Steps = "\D{Steps}"
%format Fuel = "\D{Fuel}"
%format multi = "\Con{multi}"
%format steps = "\Con{steps}"
%format done = "\Con{done}"
%format Step = "\Con{Step}"
%format Done = "\Con{Done}"
%format out-of-gas = "\Con{out\textrm{-}of\textrm{-}gas}"

\section{Evaluation}
\label{sec:eval}

Following Wadler's recipe~\cite{Wadler-plfa} to automate evaluation for the Simple Typed Lambda Calculus (STLC), we also define an evaluator for FJ, by the repeated application of the proofs of \emph{progress} and \emph{preservation}, using an Agda function that computes the reduction sequence from any given closed, well-typed expression to its value. 

First we present the inductive datatype |_↠_|, which represents the multi-step relation, or the reflexive and transitive closure of the step relation. This relation is defined as a sequence of zero (|refl|) or more steps (|multi|) of the underlying relation.

\begin{spec}
data _↠_ : Expr → Expr → Set where
  refl  : ∀ {e} → e ↠ e
  multi : ∀ {e e' e''} → e ⟶ e' → e' ↠ e'' → e ↠ e''
\end{spec}

Then, we can implement the function |eval|. Since Agda is a total language, we use a |Fuel| (represented as a natural number) to avoid non-termination. We also use two other inductive datatype definitions\footnote{For brevity, we just discuss their constructors, however the complete source-code is available on-line~\cite{repos}.} (|Finished| which has two constructors: |done| indicating that the computation is successfully finished, and |out-of-gas| indicating that the fuel ran out; and |Steps|, with one constructor: |steps| which combines the multi-step relation |_↠_| and the |Finished| datatype) to proceed with the evaluation.

\begin{spec}
eval : ∀ {e τ} → Fuel → [] ⊢ e ∶ τ → Steps e
eval zero t = steps refl out-of-gas
eval (suc fuel) t with progress t
... | Done vl = steps refl (done vl)
... | Step stp with eval fuel (preservation t stp)
...   | steps stp' fin = steps (multi stp stp') fin
\end{spec}

The |eval| function receives the fuel and evidence that |e| is a well-typed expression, and produces the |Steps| to evaluate the given expression. It starts with a closed and well-typed term. By |progress|, it is either a value, in which case we are |Done|, or it reduces to some other expression. By |preservation|, that other expression will be closed and well-typed. This process is repeated until we reach a value, or the fuel rans out~\cite{Wadler-plfa}. 

\section{Related Work}
\label{sec:rel}

There are several papers describing the mechanization of programming languages in proof assistants. For example, in their book, Pierce et al.~\cite{pierce2019software} describe the formalization of STLC in Coq, and Wadler~\cite{Wadler-plfa} present the formalization of STLC in Agda. We used their ideas to build the foundations of our encoding. Besides these books, there are several other papers mechanizing different versions of $\lambda$-calculus, among other languages~\cite{Ribeiro2013,Donnelly:2007:FSN:1247762.1248307}.

Regarding Featherweight Java, there are some projects describing its formalization. Feitosa et al.~\cite{feitosa2019-1} provided an intrinsically-typed formalization for FJ. Mackay et al.~\cite{Mackay:2012:EFJ:2318202.2318206} developed a mechanized formalization of FJ with assignment and immutability in Coq, proving type-soundness for their results. Delaware et al.~\cite{Delaware:2011:PLT:2076021.2048113} used FJ as basis to describe how to engineer product lines with theorems and proofs built from feature modules, also carrying the formalization Coq. All these papers inspired us in our modeling of FJ. The first difference between these works and ours is that we encoded the semantic rules and proofs in Agda, which is being used more frequently nowadays. Another difference is that we do not use any proof automation, since Agda's system is not as powerful as Coq's. As far as we know, our work is the first to formalize FJ in Agda using the extrinsic approach. We believe that this formalization can be used as basis to study properties of object-oriented programming languages by other researchers.

\pagebreak

\section{Conclusion}
\label{sec:conclusion}

In this paper, we presented a formalization of Featherweight Java using the Wright and Felleisen's syntactic approach to specify the static and dynamic semantics, proving the common soundness properties. As we could notice, although FJ is a small core calculus, its non-trivial binding structures and intricate relation between class tables and expressions give rise to challenges during its formalization. The Agda language has shown to be a good tool for such work, although it does not provide proof automation, which can make the maintainability process difficult for large subsets of languages and bigger proofs. During the development of this work, we have changed our definitions many times, both as a result of correcting errors and streamlining the presentation. The possibility of testing the changes by running the evaluation function helps to reason about the impact right away.

As future work, we intend to extend the formalization to embed more features of Java, like dynamic dispatch, $\lambda$-expressions and default methods, studying which features do enjoy the safety properties. We can also explore different approaches to formalize the language and extensions, and prove the equivalence with the result presented in this paper.

\section*{Acknowledgments}

We would like to thank Wouter Swierstra and Alejandro Serrano Mena from the Software Technology Group at Utrecht University for the valuable suggestions during the development of this paper.

\vspace{6pt}

This material is based upon work supported by CAPES/Brazil.

\bibliographystyle{entcs}
\bibliography{references}

\end{document}
