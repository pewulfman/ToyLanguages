"""Generate step-by-step proof frames for slides.tex.

Left column : code highlighted with Alectryon's Coq lexer, a '>' marker
              on the current line (one beamer overlay per step).
Right column: one Alectryon block per step (executed for real, input
              hidden with .no-in), shown only on its overlay.
Last overlay: a pop-up box with the slide's takeaways.

Usage (from TPP-2026-prez/):
    .venv/bin/python tools/gen_steps.py tools/out    # writes tools/out/frame*.tex
    python3 tools/insert_steps.py tools/out           # splices them into slides.tex
    make

Needs, in the slides.tex preamble: \alectryonvscode (VS Code-like goals:
"k : conclusion", hypotheses of goal 1 only), \rocqmsg (messages Alectryon
does not capture), \mk (cursor) and \popup (takeaway box).
Step kinds: normal (own overlay), SILENT (shown, run in the hidden prelude,
e.g. the statement), TAIL (shown after the last step, never run), and
msg_step (run hidden, show a Rocq message typed by hand, copied from rocq repl).
"""
import sys
from pygments import highlight
from pygments.formatters import LatexFormatter
from alectryon.pygments_lexer import CoqLexer

LEXER = CoqLexer()
FMT = LatexFormatter(nowrap=True)


def hl(line):
    out = highlight(line, LEXER, FMT).rstrip("\n")
    return out.replace(" ", "~") if out else "~"


SILENT = "SILENT"
TAIL = "TAIL"   # displayed after the last step, never run on this slide
HIDDEN = "HIDDEN"  # displayed without cursor, run in place without output (e.g. an abridged case)


def frame(title, subtitle, module, steps, final, popup, width=48, left=.55, imp="Method2", top=True):
    """steps: list of (display_lines, exec_text_or_None, right_override).
    right_override == SILENT: displayed without cursor, run in the hidden
    prelude (no overlay of its own)."""
    shown = [st for st in steps if st[2] not in (SILENT, TAIL, HIDDEN)]
    n = len(shown)
    L = []
    L.append(r"\begin{frame}[t]{%s}" % title)
    if subtitle:
        L.append("  " + subtitle)
    L.append(r"\begin{alectryon}{coq}{none}")
    L.append("Module %s.\nImport %s.\nSet Printing Width %d." % (module, imp, width))
    for lines, ex, right in steps:
        if right == SILENT:
            L.append(ex)
    L.append(r"\end{alectryon}")
    if top:
        L.append(r"  \vspace{1.5ex}")
    L.append(r"  \begin{columns}[t,totalwidth=1.06\textwidth]")
    L.append(r"    \column{%.2f\textwidth}" % left)
    L.append(r"    {\ttfamily\scriptsize\setlength{\parindent}{0pt}")
    L.append(r"    \mbox{}\\[-1pt]")  # empty first line: code a bit lower, proof state unchanged
    k = 0
    for lines, _, right in steps:
        live = right not in (SILENT, TAIL, HIDDEN)
        if live:
            k += 1
        for i, ln in enumerate(lines):
            mark = r"\mk{%d}" % k if (i == 0 and live) else r"\mk{0}"
            L.append("    " + mark + hl(ln) + r"\\")
    L.append("    }")
    L.append(r"    \column{%.2f\textwidth}" % (1.06 - left))
    L.append(r"    \alectryonvscode\vspace*{-5pt}")
    k = 0
    for lines, ex, right in steps:
        if right in (SILENT, TAIL):
            continue
        if right == HIDDEN:
            L.append(r"\begin{alectryon}{coq}{none}")
            L.append(ex)
            L.append(r"\end{alectryon}")
            continue
        k += 1
        L.append(r"    \begin{onlyenv}<%d>" % k)
        if ex is not None:
            L.append(r"\begin{alectryon}{coq}{}")
            L.append(ex)
            L.append(r"\end{alectryon}")
        if right:
            L.append("    " + right)
        L.append(r"    \end{onlyenv}")
    L.append(r"  \end{columns}")
    L.append(r"\begin{alectryon}{coq}{none}")
    L.append(final + "\nEnd %s." % module)
    L.append(r"\end{alectryon}")
    L.append(r"  \popup<%d>{%s}" % (n + 1, popup))
    L.append(r"\end{frame}")
    return "\n".join(L) + "\n"


def tac(line, extra=""):
    """Executed text of one displayed line: show its output only."""
    s = line.strip()
    if s[:2] in ("- ", "+ "):
        return "%s (* .none *) %s (* .unfold .no-in *)" % (s[0], s[2:])
    return "%s (* .unfold .no-in *)" % s


OK = r"{\color{nagoyaGreen}\small$\checkmark$ accepted}"


def err(msg):
    return (r"\colorbox{red!8}{\parbox{.95\linewidth}{\ttfamily\scriptsize %s}}" % msg)


STMT = ["Lemma type_wf Γ A (H : TypeJG Γ A) : CtxJG Γ",
        "with  subs_wf Δ Γ y (H : SubsJG Δ Γ y) :",
        "        CtxJG Δ /\\ CtxJG Γ."]
STMT_FIX = ["Fixpoint type_wf Γ A (H : TypeJG Γ A)",
            "        {struct H} : CtxJG Γ",
            "with subs_wf Δ Γ y (H : SubsJG Δ Γ y)",
            "        {struct H} :",
            "        CtxJG Δ /\\ CtxJG Γ."]
SUBS_CASE = ["- dependent induction H.",
             "  destruct IHSubsJG as [HD HG].",
             "  split; [exact HD | exact (ctx_ext _ _ HG H0)]."]


MSG_BULLET = (r"\rocqmsg{This subproof is complete, but there are some unfocused goals.\\"
              r" Focus next goal with bullet -.}")
MSG_DONE = r"\rocqmsg{No more goals.}"
MSG_PLUS = (r"\rocqmsg{This subproof is complete, but there are some unfocused goals.\\"
            r" Focus next goal with bullet +.}")


def msg_step(line, msg):
    """A step whose output Alectryon does not capture: run it, show Rocq's message."""
    s = line.strip()
    if s[:2] in ("- ", "+ "):
        ex = "%s (* .none *) %s (* .none *)" % (s[0], s[2:])
    else:
        ex = "%s (* .none *)" % s
    return ([line], ex, msg)


def stmt_step(lines):
    # the statement: shown, run silently (no overlay, no cursor)
    return (lines, "\n".join(lines), SILENT)


def simple(line):
    return ([line], tac(line), None)


PROOF = (["Proof."], "Proof. (* .unfold .no-in -.g#2.h{*} *)", None)

# The slides use an abridged syntax: each dependent induction has one real
# case; the other cases of the full 2.3 syntax are shown as "+ (* abridged *)"
# (displayed, never run) and the messages are those of the full proof
# ("Focus next goal with bullet +.", checked in Rocq).
ABRIDGED = (["  + (* abridged *)"], None, TAIL)
SUBS_STEPS = [(["- dependent induction H."],
               "- (* .none *) dependent induction H. (* .unfold .no-in -.g#2.h{*} *)", None),
              simple("  + pose proof (type_wf _ _ H) as HG."),
              msg_step("    split; [exact (ctx_ext _ _ HG H) | exact HG].", MSG_PLUS),
              (["  + (* abridged *)"],
               "+ destruct IHSubsJG as [HD HG].\n  split; [exact HD | exact (ctx_ext _ _ HG H0)].",
               HIDDEN)]

good = [stmt_step(STMT), PROOF,
        simple("- dependent induction H."),
        msg_step("  + exact (proj1 (subs_wf _ _ _ H)).", MSG_PLUS),
        ABRIDGED] + SUBS_STEPS + \
       [(["Qed."], "Qed. (* .none *)", OK)]

bad_body = [PROOF,
            msg_step("- exact (type_wf Γ A H).  (* accepted *)", MSG_BULLET)] + SUBS_STEPS

GUARDED = (["  Guarded."], "Fail Guarded. (* .none *)",
           err(r"Error: Recursive definition of type\_wf and subs\_wf is ill-formed.\\"
               r" As a mutual fixpoint decreasing on the 1st argument of type\_wf and"
               r" 1st argument of subs\_wf: Recursive call to type\_wf has principal"
               r' argument equal to "Γ" instead of a subterm of "Γ".\\'
               r" As a mutual fixpoint decreasing on the 1st argument of type\_wf and"
               r" 2nd argument of subs\_wf: \dots\\ \dots") +
           r"\\{\tiny (error abridged: 12 combinations, 64 lines)}")

bad = [stmt_step(STMT)] + bad_body + \
      [(["Qed."], "Fail Qed. (* .none *)",
        err(r"Error: Cannot guess decreasing argument of fix."))]

# same proof, checkpoint right after the suspicious line; stop on its error
guarded = [stmt_step(STMT)] + bad_body[:2] + [GUARDED] + \
          [(lines, None, TAIL) for lines, _, _ in bad_body[2:]] + [(["Qed."], None, TAIL)]

GUARDED_FIX = (["  Guarded."], "Fail Guarded. (* .none *)",
               err(r"Error: Recursive definition of type\_wf and subs\_wf is ill-formed.\\"
                   r" As a mutual fixpoint decreasing on the 3rd argument of type\_wf and"
                   r" 4th argument of subs\_wf: Recursive call to type\_wf has principal"
                   r' argument equal to "H" instead of a subterm of "H".\\ \dots') +
               r"\\{\tiny (error abridged: 1 combination, 9 lines)}")

fix = [stmt_step(STMT_FIX)] + bad_body[:2] + [GUARDED_FIX] + bad_body[2:] + \
      [(["Qed."], "Fail Qed. (* .none *)",
        err(r"Error: Recursive definition of type\_wf is ill-formed.\\ \dots\\"
            r" Recursive call to type\_wf has principal argument equal to"
            r' "H" instead of a subterm of "H".') +
        r"\\{\tiny (error abridged)}")]

MOTIVE = ["Definition wf_motive (f : Sort) : Prop :=",
          "  match f with",
          "  | TY Γ _   => J (CX Γ)",
          "  | SB Δ Γ _ => J (CX Δ) /\\ J (CX Γ)",
          "  | TM Γ _ _ => J (CX Γ)",
          "  | _        => True",
          "  end."]
HIDE234 = "-.g#2.h{*} -.g#3.h{*} -.g#4.h{*} -.g#5.h{*}"
WHOLE = [(MOTIVE, "\n".join(MOTIVE), SILENT),
         (["Lemma wf_all f (H : J f) : wf_motive f."],
          "Lemma wf_all f (H : J f) : wf_motive f.", SILENT),
         (["Proof."], "Proof. (* .unfold .no-in *)", None),
         (["  induction H; simpl in *."],
          "induction H; simpl in *. (* .unfold .no-in %s *)" % HIDE234, None),
         msg_step("  - trivial.", MSG_BULLET),
         (["  -"], "- (* .unfold .no-in *)", None),
         msg_step("    exact (proj1 IHJ1).", MSG_BULLET),
         msg_step("  - exact (proj1 IHJ1).", MSG_BULLET),
         msg_step("  - split; [exact (ctx_ext _ _ IHJ H) | exact IHJ].", MSG_BULLET),
         (["  -"], "- (* .unfold .no-in *)", None),
         msg_step("    split; [exact IHJ3 | exact (ctx_ext _ _ IHJ2 H0)].", MSG_DONE),
         (["Qed."], "Qed. (* .none *)", OK)]
WHOLE_FINAL = "Lemma wf Γ A (H : J (TY Γ A)) : J (CX Γ).\nProof. exact (wf_all _ H). Qed."

POPS2 = r"""\begin{itemize}
      \item no \texttt{fix} in the proof: no termination check at \texttt{Qed}
      \item method 2 gets the same with \texttt{Combined Scheme}
      \item (c) done right: the induction comes \emph{before} the cases
    \end{itemize}"""

POP11 = r"""\begin{itemize}
      \item combine only the lemmas that depend on each other
      \item they are all \textbf{in the context}, ready to be used
      \item scales well: no duplication, no boilerplate
    \end{itemize}"""
POP13 = r"""\begin{itemize}
      \item more freedom, less guidance: termination is checked only at \texttt{Qed}.
      \item the error says neither which lemma nor which line
    \end{itemize}"""
POP13B = r"""\begin{itemize}
      \item \texttt{Guarded.}: check \emph{now}, as a checkpoint
      \item but it tries \textbf{every} combination of decreasing arguments:
            here $3 \times 4 = 12$ combinations, 64 lines of error
      \item exponential in the number of lemmas
    \end{itemize}"""
POP14 = r"""\begin{itemize}
      \item one combination checked; the error names the lemma and the bad call
      \item \texttt{Guarded.} too: 1 combination, 9 lines (12 combinations, 64 lines without \texttt{struct})
      \item trade-off: you must know the decreasing argument \emph{before} the proof
    \end{itemize}"""

out = {
    "11": frame(r"(d) Mutual lemmas: \texttt{Lemma \dots\ with \dots}", "",
                "Mut", good, "", POP11),
    "13": frame(r"With great power comes great responsibility",
                r"A circular ``proof'' is accepted, step by step\dots",
                "Bad", bad, "Abort.", POP13),
    "13b": frame(r"Checking early: \texttt{Guarded.}",
                 r"Same proof, with a checkpoint after the suspicious line.",
                 "Grd", guarded, "Abort.", POP13B),
    "14": frame(r"Supplement: \texttt{Fixpoint \dots\ \{struct H\}} with no body",
                r"Also enters proof mode, but the decreasing argument is \textbf{given}.",
                "Fix", fix, "Abort.", POP14),
}
out["S2"] = frame(r"Looking back: an induction principle, no termination check",
                  "",
                  "Whole", WHOLE, WHOLE_FINAL, POPS2, imp="Method1", top=False)

for k, v in out.items():
    open(sys.argv[1] + "/frame%s.tex" % k, "w").write(v)
