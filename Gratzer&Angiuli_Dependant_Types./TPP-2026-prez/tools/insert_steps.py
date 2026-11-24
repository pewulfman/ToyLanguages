import sys
S = sys.argv[1]
p = 'slides.tex'
s = open(p).read()
anchor = r'''\newcommand\alectryonscriptoutput{\renewcommand*{\alectryon@output@setsize}{\scriptsize}}
\makeatother
'''
macros = r'''% step-by-step proofs: \mk{k} = cursor shown on overlay k (0 = never)
\newcommand\mk[1]{\makebox[1.1em][l]{\ifnum#1>0 \alt<#1>{\textcolor{nagoyaGreen}{\textbf{>}}}{}\fi}}
% \popup<k>{...}: takeaway box over the slide on overlay k
\usetikzlibrary{shadows}
\newcommand<>\popup[1]{\only#2{\begin{tikzpicture}[remember picture,overlay]
  \node[fill=white, draw=nagoyaGreen, very thick, rounded corners, drop shadow,
        inner sep=10pt] at (current page.center)
        {\begin{minipage}{.7\paperwidth}\small #1\end{minipage}};
\end{tikzpicture}}}
'''
assert anchor in s
if r'\newcommand\mk' not in s:
    s = s.replace(anchor, anchor + macros, 1)
for k, start, end in [('11', '% --- [Mutual]', '% --- [Level]'),
                      ('13', '% --- [Power]', '% --- [Guarded]'),
                      ('13b', '% --- [Guarded]', '% --- [M1-whole]'),
                      ('S2', '% --- [M1-whole]', '% --- [Takeaways]'),
                      ('14', '% --- [Supp-Fix]', '% --- [Supp-M1-ind]')]:
    a = s.index(start)
    b = s.index(end)
    f = s.index(r'\begin{frame}', a)
    s = s[:a] + s[a:f] + open(S + '/frame%s.tex' % k).read() + '\n' + s[b:]
open(p, 'w').write(s)
