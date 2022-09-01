Here we collect some information on how to set up your editor to properly input
and output the unicode characters used throughout Iris.

If you really want to, you can also avoid having to type unicode characters by
importing `iris.bi.ascii`.  That enables parsing-only ASCII alternatives to many
unicode notations. (Feel free to report an issue when you notice that a notation
is missing.)  The easiest way to learn the ASCII syntax is to
[read this file](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/theories/bi/ascii.v).
Note however that this will make your code harder to read and work on for Iris
developers that are used to our default unicode notation---generally, our
recommendation is to use the unicode syntax whenever possible. In particular,
Unicode syntax is required for MRs to Iris itself and other Iris-managed
repositories.

## General: Unicode Fonts

Most editors will just use system fonts for rendering unicode characters and do
not need further configuration once the fonts are installed.  Here are some
combinations of fonts that are known to give readable results (i.e., each of
these sets of fonts covers all the required characters):

* Fira Mono, DejaVu Mono, Symbola

## Emacs

### Unicode Input

First, install `math-symbol-lists` by doing `M-x package-install math-symbol-lists`.

Next, add the following to your `~/.emacs` to configure an input method based
on the math symbol list, and with some custom aliases for symbols used a lot in Iris:
```
;; Input of unicode symbols
(require 'math-symbol-lists)
; Automatically use math input method for Coq files
(add-hook 'coq-mode-hook (lambda () (set-input-method "math")))
; Input method for the minibuffer
(defun my-inherit-input-method ()
  "Inherit input method from `minibuffer-selected-window'."
  (let* ((win (minibuffer-selected-window))
         (buf (and win (window-buffer win))))
    (when buf
      (activate-input-method (buffer-local-value 'current-input-method buf)))))
(add-hook 'minibuffer-setup-hook #'my-inherit-input-method)
; Define the actual input method
(quail-define-package "math" "UTF-8" "Ω" t)
(quail-define-rules ; add whatever extra rules you want to define here...
 ("\\fun"    ?λ)
 ("\\mult"   ?⋅)
 ("\\ent"    ?⊢)
 ("\\valid"  ?✓)
 ("\\diamond" ?◇)
 ("\\box"    ?□)
 ("\\bbox"   ?■)
 ("\\later"  ?▷)
 ("\\pred"   ?φ)
 ("\\and"    ?∧)
 ("\\or"     ?∨)
 ("\\comp"   ?∘)
 ("\\ccomp"  ?◎)
 ("\\all"    ?∀)
 ("\\ex"     ?∃)
 ("\\to"     ?→)
 ("\\sep"    ?∗)
 ("\\lc"     ?⌜)
 ("\\rc"     ?⌝)
 ("\\Lc"     ?⎡)
 ("\\Rc"     ?⎤)
 ("\\lam"    ?λ)
 ("\\empty"  ?∅)
 ("\\Lam"    ?Λ)
 ("\\Sig"    ?Σ)
 ("\\-"      ?∖)
 ("\\aa"     ?●)
 ("\\af"     ?◯)
 ("\\auth"   ?●)
 ("\\frag"   ?◯)
 ("\\iff"    ?↔)
 ("\\gname"  ?γ)
 ("\\incl"   ?≼)
 ("\\latert" ?▶)
 ("\\update" ?⇝)

 ;; accents (for iLöb)
 ("\\\"o" ?ö)

 ;; subscripts and superscripts
 ("^^+" ?⁺) ("__+" ?₊) ("^^-" ?⁻)
 ("__0" ?₀) ("__1" ?₁) ("__2" ?₂) ("__3" ?₃) ("__4" ?₄)
 ("__5" ?₅) ("__6" ?₆) ("__7" ?₇) ("__8" ?₈) ("__9" ?₉)

 ("__a" ?ₐ) ("__e" ?ₑ) ("__h" ?ₕ) ("__i" ?ᵢ) ("__k" ?ₖ)
 ("__l" ?ₗ) ("__m" ?ₘ) ("__n" ?ₙ) ("__o" ?ₒ) ("__p" ?ₚ)
 ("__r" ?ᵣ) ("__s" ?ₛ) ("__t" ?ₜ) ("__u" ?ᵤ) ("__v" ?ᵥ) ("__x" ?ₓ)
)
(mapc (lambda (x)
        (if (cddr x)
            (quail-defrule (cadr x) (car (cddr x)))))
      (append math-symbol-list-basic math-symbol-list-extended))
```

Finally, set your default input method with `M-x customize-set-value`, setting
`default-input-method` to `math`.

### Font Configuration

Even when usable fonts are installed, Emacs tends to pick bad fonts for some
symbols like universal and existential quantifiers.  The following configuration
results in a decent choice for the symbols used in Iris:

```
;; Fonts
(set-face-attribute 'default nil :height 110) ; height is in 1/10pt
(dolist (ft (fontset-list))
  ; Main font
  (set-fontset-font ft 'unicode (font-spec :name "Monospace"))
  ; Fallback font
  ; Appending to the 'unicode list makes emacs unbearably slow.
  ;(set-fontset-font ft 'unicode (font-spec :name "DejaVu Sans Mono") nil 'append)
  (set-fontset-font ft nil (font-spec :name "DejaVu Sans Mono"))
)
; Fallback-fallback font
; If we 'append this to all fontsets, it picks Symbola even for some cases where DejaVu could
; be used. Adding it only to the "t" table makes it Do The Right Thing (TM).
(set-fontset-font t nil (font-spec :name "Symbola"))
```

## CoqIDE 8.9 and earlier on Linux (ibus-m17n)

On Linux with old versions of CoqIDE you can use the Intelligent
Input Bus (IBus) framework to input Unicode symbols. First, install `ibus-m17n`
via your system's package manager. Next, create a file `~/.m17n.d/coq.mim` to
configure an input method based on the math symbol list, and with some custom
aliases for symbols used a lot in Iris:

```
;; Usage: copy to ~/.m17n.d/coq.mim

(input-method t coq)
(description "Input method for Coq")
(title "Coq")

(map (trans

;; Standard LaTeX math notations
  ("\\forall"         "∀")
  ("\\exists"         "∃")
  ("\\lam"            "λ")
  ("\\not"            "¬")
  ("\\/"              "∨")
  ("/\\"              "∧")
  ("->"               "→")
  ("<->"              "↔")
  ("\\<-"             "←") ;; we add a backslash because the plain <- is used for the rewrite tactic
  ("\\=="             "≡")
  ("\\/=="            "≢")
  ("/="               "≠")
  ("<="               "≤")
  ("\\in"             "∈")
  ("\\notin"          "∉")
  ("\\cup"            "∪")
  ("\\cap"            "∩")
  ("\\setminus"       "∖")
  ("\\subset"         "⊂")
  ("\\subseteq"       "⊆")
  ("\\sqsubseteq"     "⊑")
  ("\\sqsubseteq"     "⊑")
  ("\\notsubseteq"    "⊈")
  ("\\meet"           "⊓")
  ("\\join"           "⊔")
  ("\\top"            "⊤")
  ("\\bottom"         "⊥")
  ("\\vdash"          "⊢")
  ("\\dashv"          "⊣")
  ("\\Vdash"          "⊨")
  ("\\infty"          "∞")
  ("\\comp"           "∘")
  ("\\prf"            "↾")
  ("\\bind"           "≫=")
  ("\\mapsto"         "↦")
  ("\\hookrightarrow" "↪")
  ("\\uparrow"        "↑")

;; Iris specific
  ("\\fun"            "λ")
  ("\\mult"           "⋅")
  ("\\ent"            "⊢")
  ("\\valid"          "✓")
  ("\\diamond"        "◇")
  ("\\box"            "□")
  ("\\bbox"           "■")
  ("\\later"          "▷")
  ("\\pred"           "φ")
  ("\\and"            "∧")
  ("\\or"             "∨")
  ("\\comp"           "∘")
  ("\\ccomp"          "◎")
  ("\\all"            "∀")
  ("\\ex"             "∃")
  ("\\to"             "→")
  ("\\sep"            "∗")
  ("\\lc"             "⌜")
  ("\\rc"             "⌝")
  ("\\Lc"             "⎡")
  ("\\Rc"             "⎤")
  ("\\empty"          "∅")
  ("\\Lam"            "Λ")
  ("\\Sig"            "Σ")
  ("\\-"              "∖")
  ("\\aa"             "●")
  ("\\af"             "◯")
  ("\\auth"           "●")
  ("\\frag"           "◯")
  ("\\iff"            "↔")
  ("\\gname"          "γ")
  ("\\incl"           "≼")
  ("\\latert"         "▶")
  ("\\update"         "⇝")
  ("\\bind"           "≫=")

;; accents (for iLöb)
  ("\\\"o" "ö")

;; subscripts and superscripts
  ("^^+" "⁺") ("__+" "₊") ("^^-" "⁻")
  ("__0" "₀") ("__1" "₁") ("__2" "₂") ("__3" "₃") ("__4" "₄")
  ("__5" "₅") ("__6" "₆") ("__7" "₇") ("__8" "₈") ("__9" "₉")

  ("__a" "ₐ") ("__e" "ₑ") ("__h" "ₕ") ("__i" "ᵢ") ("__k" "ₖ")
  ("__l" "ₗ") ("__m" "ₘ") ("__n" "ₙ") ("__o" "ₒ") ("__p" "ₚ")
  ("__r" "ᵣ") ("__s" "ₛ") ("__t" "ₜ") ("__u" "ᵤ") ("__v" "ᵥ") ("__x" "ₓ")

;; Greek alphabet
  ("\\Alpha"  "Α")   ("\\alpha"  "α")
  ("\\Beta"   "Β")   ("\\beta"   "β")
  ("\\Gamma"  "Γ")   ("\\gamma"  "γ")
  ("\\Delta"  "Δ")   ("\\delta"  "δ")
  ("\\Epsilon"  "Ε") ("\\epsilon"  "ε")
  ("\\Zeta"   "Ζ")   ("\\zeta"   "ζ")
  ("\\Eta"  "Η")     ("\\eta"  "η")
  ("\\Theta"  "Θ")   ("\\theta"  "θ")
  ("\\Iota"   "Ι")   ("\\iota"   "ι")
  ("\\Kappa"  "Κ")   ("\\kappa"  "κ")
  ("\\Lamda"  "Λ")   ("\\lamda"  "λ")
  ("\\Lambda"   "Λ") ("\\lambda"   "λ")
  ("\\Mu"   "Μ")     ("\\mu"   "μ")
  ("\\Nu"   "Ν")     ("\\nu"   "ν")
  ("\\Xi"   "Ξ")     ("\\xi"   "ξ")
  ("\\Omicron"  "Ο") ("\\omicron"  "ο")
  ("\\Pi"   "Π")     ("\\pi"   "π")
  ("\\Rho"  "Ρ")     ("\\rho"  "ρ")
  ("\\Sigma"  "Σ")   ("\\sigma"  "σ")
  ("\\Tau"  "Τ")     ("\\tau"  "τ")
  ("\\Upsilon"  "Υ") ("\\upsilon"  "υ")
  ("\\Phi"  "Φ")     ("\\phi"  "φ")
  ("\\Chi"  "Χ")     ("\\chi"  "χ")
  ("\\Psi"  "Ψ")     ("\\psi"  "ψ")
  ("\\Omega"  "Ω")   ("\\omega"  "ω")
))
(state (init (trans)))
```

To use this input method, you should:

1. Enable the "Coq" input using your system settings or using the IBus
   configuration tool. The Coq input method typically appears in the category
   "other".
2. On some systems: In CoqIDE, you have to enable the input method by performing
   a right click on the text area, and selecting "System (IBus)" under "input
   method".

## CoqIDE 8.10+ Unicode input

Instead of configuring the input system-wide, you can use CoqIDE's support for
inputting Unicode symbols (introduced in Coq v8.10). To input a symbol, type a
LaTeX-like escape sequence, for example `\alpha` and then type
`<Shift>-<Space>`, which will expand it into `α`. Expansion will work on a
prefix of the command as well. You can also customize the expansion keyboard
shortcut, which is under Tools/LaTeX-to-unicode.

This system is configurable by adding a Unicode bindings file with additional
expansion sequences. On Linux this file should go in
`~/.config/coq/coqide.bindings` while on macOS it should go in
`~/Library/Application Support/Coq/coqide.bindings` (or under `$XDG_CONFIG_HOME`
if you have that set).

Here is a `coqide.bindings` file for a variety of symbols used in Iris:

```
# LaTeX-like sequences are natively supported (eg, \forall, \mapsto)
# Iris-specific abbreviations
\fun            λ
\mult           ⋅ 1
\ent            ⊢ 1
\valid          ✓
\diamond        ◇
\box            □ 1
\bbox           ■
\later          ▷
\pred           φ
\and            ∧
\or             ∨
\comp           ∘ 1
\ccomp          ◎
\all            ∀
\ex             ∃
\to             →
\sep            ∗
\lc             ⌜ 1
\rc             ⌝ 1
\Lc             ⎡ 1
\Rc             ⎤ 1
\lam            λ
\empty          ∅
\Lam            Λ
\Sig            Σ
\-              ∖ 1
\aa             ● 1
\af             ◯ 1
\auth           ●
\frag           ◯
\iff            ↔ 1
\gname          γ
\incl           ≼
\latert         ▶
\update         ⇝
# accents
\"o             ö
\Lob            Löb
# subscripts and superscripts
\^+             ⁺
\_+             ₊
\^-             ⁻
\_0             ₀
\_1             ₁
\_2             ₂
\_3             ₃
\_4             ₄
\_5             ₅
\_6             ₆
\_7             ₇
\_8             ₈
\_9             ₉
\_a             ₐ
\_e             ₑ
\_h             ₕ
\_i             ᵢ
\_k             ₖ
\_l             ₗ
\_m             ₘ
\_n             ₙ
\_o             ₒ
\_p             ₚ
\_r             ᵣ
\_s             ₛ
\_t             ₜ
\_u             ᵤ
\_v             ᵥ
\_x             ₓ
```

## Visual Studio Code

### VSCoq setup

The recommended extension as of December 2019 is [Maxime Dénès's
VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).
Press `Ctrl Shift P` or `Cmd Shift P` and then type "coq" to see the list of Coq
commands and keyboard shortcuts.

### Font setup

To use unicode you need a font that supports all the symbols, such as [Fira
Code](https://github.com/tonsky/FiraCode/wiki/Installing). Download and install
the font, and in VS Code press `Cmd ,` or `Ctrl ,` to go to the settings, search
for "font", and use "FiraCode-Retina" as the font-family and optionally enable
ligatures.

### Unicode input setup

Install the [Generic input method
extension](https://marketplace.visualstudio.com/items?itemName=mr-konn.generic-input-method).
To insert a symbol, type the code for a symbol such as `\to` and then press
`Space` or `Tab`. To enable Iris unicode input support, open your user settings,
press `Cmd ,` or `Ctrl ,`, type "generic-input-methods.input-methods", and then
click on "Edit in settings.json" and add the following:

```
  "generic-input-methods.input-methods": [
        {
            "name": "Iris Math",
            "commandName": "text.math",
            "languages": [
                "coq"
            ],
            "triggers": [
                "\\"
            ],
            "dictionary": [
                // Standard LaTeX math notations
                { "label": "forall", "body": "∀", "description": "∀" },
                { "label": "exists", "body": "∃", "description": "∃" },
                { "label": "lam", "body": "λ", "description": "λ" },
                { "label": "not", "body": "¬", "description": "¬" },
                { "label": "->", "body": "→", "description": "→" },
                { "label": "<->", "body": "↔", "description": "↔" },
                { "label": "<-", "body": "←", "description": "←" },
                { "label": "==", "body": "≡", "description": "≡" },
                { "label": "/==", "body": "≢", "description": "≢" },
                { "label": "/=", "body": "≠", "description": "≠" },
                { "label": "neq", "body": "≠", "description": "≠" },
                { "label": "nequiv", "body": "≢", "description": "≢" },
                { "label": "<=", "body": "≤", "description": "≤" },
                { "label": "leq", "body": "≤", "description": "≤" },
                { "label": "in", "body": "∈", "description": "∈" },
                { "label": "notin", "body": "∉", "description": "∉" },
                { "label": "cup", "body": "∪", "description": "∪" },
                { "label": "cap", "body": "∩", "description": "∩" },
                { "label": "setminus", "body": "∖", "description": "∖" },
                { "label": "subset", "body": "⊂", "description": "⊂" },
                { "label": "subseteq", "body": "⊆", "description": "⊆" },
                { "label": "sqsubseteq", "body": "⊑", "description": "⊑" },
                { "label": "sqsubseteq", "body": "⊑", "description": "⊑" },
                { "label": "notsubseteq", "body": "⊈", "description": "⊈" },
                { "label": "meet", "body": "⊓", "description": "⊓" },
                { "label": "join", "body": "⊔", "description": "⊔" },
                { "label": "top", "body": "⊤", "description": "⊤" },
                { "label": "bottom", "body": "⊥", "description": "⊥" },
                { "label": "vdash", "body": "⊢", "description": "⊢" },
                { "label": "|-", "body": "⊢", "description": "⊢" },
                { "label": "dashv", "body": "⊣", "description": "⊣" },
                { "label": "Vdash", "body": "⊨", "description": "⊨" },
                { "label": "infty", "body": "∞", "description": "∞" },
                { "label": "comp", "body": "∘", "description": "∘" },
                { "label": "prf", "body": "↾", "description": "↾" },
                { "label": "bind", "body": "≫=", "description": "≫=" },
                { "label": "mapsto", "body": "↦", "description": "↦" },
                { "label": "hookrightarrow", "body": "↪", "description": "↪" },
                { "label": "uparrow", "body": "↑", "description": "↑" },

                // Iris specific
                { "label": "fun", "body": "λ", "description": "λ" },
                { "label": "mult", "body": "⋅", "description": "⋅" },
                { "label": "ent", "body": "⊢", "description": "⊢" },
                { "label": "valid", "body": "✓", "description": "✓" },
                { "label": "diamond", "body": "◇", "description": "◇" },
                { "label": "box", "body": "□", "description": "□" },
                { "label": "bbox", "body": "■", "description": "■" },
                { "label": "later", "body": "▷", "description": "▷" },
                { "label": "pred", "body": "φ", "description": "φ" },
                { "label": "and", "body": "∧", "description": "∧" },
                { "label": "or", "body": "∨", "description": "∨" },
                { "label": "comp", "body": "∘", "description": "∘" },
                { "label": "ccomp", "body": "◎", "description": "◎" },
                { "label": "all", "body": "∀", "description": "∀" },
                { "label": "ex", "body": "∃", "description": "∃" },
                { "label": "to", "body": "→", "description": "→" },
                { "label": "sep", "body": "∗", "description": "∗" },
                { "label": "star", "body": "∗", "description": "∗" },
                { "label": "lc", "body": "⌜", "description": "⌜" },
                { "label": "rc", "body": "⌝", "description": "⌝" },
                { "label": "Lc", "body": "⎡", "description": "⎡" },
                { "label": "Rc", "body": "⎤", "description": "⎤" },
                { "label": "empty", "body": "∅", "description": "∅" },
                { "label": "Lam", "body": "Λ", "description": "Λ" },
                { "label": "Sig", "body": "Σ", "description": "Σ" },
                { "label": "-", "body": "∖", "description": "∖" },
                { "label": "aa", "body": "●", "description": "●" },
                { "label": "af", "body": "◯", "description": "◯" },
                { "label": "auth", "body": "●", "description": "●" },
                { "label": "frag", "body": "◯", "description": "◯" },
                { "label": "iff", "body": "↔", "description": "↔" },
                { "label": "gname", "body": "γ", "description": "γ" },
                { "label": "incl", "body": "≼", "description": "≼" },
                { "label": "latert", "body": "▶", "description": "▶" },
                { "label": "update", "body": "⇝", "description": "⇝" },
                { "label": "bind", "body": "≫=", "description": "≫=" },

                // accents (for iLöb)
                { "label": "\"o", "body": "ö", "description": "ö" },

                // subscripts and superscripts
                { "label": "^^+", "body": "⁺", "description": "⁺" },
                { "label": "__+", "body": "₊", "description": "₊" },
                { "label": "^^-", "body": "⁻", "description": "⁻" },
                { "label": "__0", "body": "₀", "description": "₀" },
                { "label": "__1", "body": "₁", "description": "₁" },
                { "label": "__2", "body": "₂", "description": "₂" },
                { "label": "__3", "body": "₃", "description": "₃" },
                { "label": "__4", "body": "₄", "description": "₄" },
                { "label": "__5", "body": "₅", "description": "₅" },
                { "label": "__6", "body": "₆", "description": "₆" },
                { "label": "__7", "body": "₇", "description": "₇" },
                { "label": "__8", "body": "₈", "description": "₈" },
                { "label": "__9", "body": "₉", "description": "₉" },
                { "label": "__a", "body": "ₐ", "description": "ₐ" },
                { "label": "__e", "body": "ₑ", "description": "ₑ" },
                { "label": "__h", "body": "ₕ", "description": "ₕ" },
                { "label": "__i", "body": "ᵢ", "description": "ᵢ" },
                { "label": "__k", "body": "ₖ", "description": "ₖ" },
                { "label": "__l", "body": "ₗ", "description": "ₗ" },
                { "label": "__m", "body": "ₘ", "description": "ₘ" },
                { "label": "__n", "body": "ₙ", "description": "ₙ" },
                { "label": "__o", "body": "ₒ", "description": "ₒ" },
                { "label": "__p", "body": "ₚ", "description": "ₚ" },
                { "label": "__r", "body": "ᵣ", "description": "ᵣ" },
                { "label": "__s", "body": "ₛ", "description": "ₛ" },
                { "label": "__t", "body": "ₜ", "description": "ₜ" },
                { "label": "__u", "body": "ᵤ", "description": "ᵤ" },
                { "label": "__v", "body": "ᵥ", "description": "ᵥ" },
                { "label": "__x", "body": "ₓ", "description": "ₓ" },

                // Greek alphabet
                { "label": "Alpha", "body": "Α", "description": "Α" },
                { "label": "alpha", "body": "α", "description": "α" },
                { "label": "Beta", "body": "Β", "description": "Β" },
                { "label": "beta", "body": "β", "description": "β" },
                { "label": "Gamma", "body": "Γ", "description": "Γ" },
                { "label": "gamma", "body": "γ", "description": "γ" },
                { "label": "Delta", "body": "Δ", "description": "Δ" },
                { "label": "delta", "body": "δ", "description": "δ" },
                { "label": "Epsilon", "body": "Ε", "description": "Ε" },
                { "label": "epsilon", "body": "ε", "description": "ε" },
                { "label": "Zeta", "body": "Ζ", "description": "Ζ" },
                { "label": "zeta", "body": "ζ", "description": "ζ" },
                { "label": "Eta", "body": "Η", "description": "Η" },
                { "label": "eta", "body": "η", "description": "η" },
                { "label": "Theta", "body": "Θ", "description": "Θ" },
                { "label": "theta", "body": "θ", "description": "θ" },
                { "label": "Iota", "body": "Ι", "description": "Ι" },
                { "label": "iota", "body": "ι", "description": "ι" },
                { "label": "Kappa", "body": "Κ", "description": "Κ" },
                { "label": "kappa", "body": "κ", "description": "κ" },
                { "label": "Lamda", "body": "Λ", "description": "Λ" },
                { "label": "lamda", "body": "λ", "description": "λ" },
                { "label": "Lambda", "body": "Λ", "description": "Λ" },
                { "label": "lambda", "body": "λ", "description": "λ" },
                { "label": "Mu", "body": "Μ", "description": "Μ" },
                { "label": "mu", "body": "μ", "description": "μ" },
                { "label": "Nu", "body": "Ν", "description": "Ν" },
                { "label": "nu", "body": "ν", "description": "ν" },
                { "label": "Xi", "body": "Ξ", "description": "Ξ" },
                { "label": "xi", "body": "ξ", "description": "ξ" },
                { "label": "Omicron", "body": "Ο", "description": "Ο" },
                { "label": "omicron", "body": "ο", "description": "ο" },
                { "label": "Pi", "body": "Π", "description": "Π" },
                { "label": "pi", "body": "π", "description": "π" },
                { "label": "Rho", "body": "Ρ", "description": "Ρ" },
                { "label": "rho", "body": "ρ", "description": "ρ" },
                { "label": "Sigma", "body": "Σ", "description": "Σ" },
                { "label": "sigma", "body": "σ", "description": "σ" },
                { "label": "Tau", "body": "Τ", "description": "Τ" },
                { "label": "tau", "body": "τ", "description": "τ" },
                { "label": "Upsilon", "body": "Υ", "description": "Υ" },
                { "label": "upsilon", "body": "υ", "description": "υ" },
                { "label": "Phi", "body": "Φ", "description": "Φ" },
                { "label": "phi", "body": "φ", "description": "φ" },
                { "label": "Chi", "body": "Χ", "description": "Χ" },
                { "label": "chi", "body": "χ", "description": "χ" },
                { "label": "Psi", "body": "Ψ", "description": "Ψ" },
                { "label": "psi", "body": "ψ", "description": "ψ" },
                { "label": "Omega", "body": "Ω", "description": "Ω" },
                { "label": "omega", "body": "ω", "description": "ω" }
            ]
        }
    ]
```
