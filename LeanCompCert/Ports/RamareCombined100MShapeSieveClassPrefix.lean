import LeanCompCert.Ports.RamareCombined100MShapeSieveMark


namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.R2SegSieve
  (markBudget markBudget_lt_word markBudget_add_len_lt_word)

/-! ## Classification

The output register convention matches `Shape`: `100..105` are
`p,pExp,rest,q,qExp,tail`.  Product planes avoid an exponentiation loop.
-/

def Cfg.classOffsetBody (c : Cfg) : List Instr :=
  let T := c.markSteps
  [ .binop 130 .sub (.reg rR) (.lit T)
  , .binop 131 .mul (.reg 11) (.reg 130) ]

def Cfg.classCandidateBody : List Instr :=
  [ .binop 132 .add (.reg 131) (.reg rW) ]

def Cfg.classPlaneBody (c : Cfg) : List Instr :=
  let L := c.segLen
  [ .binop 133 .add (.reg 131) (.lit L)
  , .binop 134 .add (.reg 131) (.lit (2 * L))
  , .binop 135 .add (.reg 131) (.lit (3 * L))
  , .binop 136 .add (.reg 131) (.lit (4 * L))
  , .binop 137 .add (.reg 131) (.lit (5 * L))
  , .binop 138 .add (.reg 131) (.lit (6 * L)) ]

/-- During the mark phase the classification loads/stores go to the same
seven sinks as inactive marks.  In particular, they must not clear cell zero
while the prime-power cursor is still filling the window. -/
def Cfg.classSinkBody (c : Cfg) : List Instr :=
  let L := c.segLen
  [ .binop 130 .mul (.reg 10) (.lit (7 * L))
  , .binop 131 .add (.reg 131) (.reg 130)
  , .binop 133 .add (.reg 133) (.reg 130)
  , .binop 134 .add (.reg 134) (.reg 130)
  , .binop 135 .add (.reg 135) (.reg 130)
  , .binop 136 .add (.reg 136) (.reg 130)
  , .binop 137 .add (.reg 137) (.reg 130)
  , .binop 138 .add (.reg 138) (.reg 130) ]

def Cfg.classLoadBody : List AInstr :=
  [ .load 140 131, .load 141 133, .load 142 134, .load 143 135
  , .load 144 136, .load 145 137, .load 146 138
  ]

def Cfg.classNormalizeBody : List Instr :=
  [ .binop 147 .eq (.reg 140) (.lit 0)
  , .binop 148 .add (.reg 140) (.reg 147)               -- allProd
  , .binop 149 .eq (.reg 141) (.lit 0)                  -- no small prime
  , .binop 150 .sub (.lit 1) (.reg 149)
  , .binop 151 .eq (.reg 143) (.lit 0)
  , .binop 152 .add (.reg 143) (.reg 151) ]             -- pProd

def Cfg.classFirstShapeBody : List Instr :=
  [ .binop 153 .udiv (.reg 132) (.reg 152)
  , .binop 154 .mul (.reg 150) (.reg 153)               -- marked rest
  , .binop rShapeP .mul (.reg 150) (.reg 141)
  , .binop 155 .mul (.reg 149) (.reg 132)
  , .binop rShapeP .add (.reg rShapeP) (.reg 155)
  , .binop rShapePE .mul (.reg 150) (.reg 142)
  , .binop 156 .mul (.reg 149) (.lit 1)
  , .binop rShapePE .add (.reg rShapePE) (.reg 156)
  , .binop rShapeRest .add (.reg 154) (.reg 149) ]

def Cfg.classSecondFlagsBody : List Instr :=
  [ .binop 157 .eq (.reg rShapeRest) (.lit 1)
  , .binop 158 .sub (.lit 1) (.reg 157)
  , .binop 159 .eq (.reg 144) (.lit 0)
  , .binop 160 .mul (.reg 158) (.reg 159)               -- large q
  , .binop 161 .sub (.lit 1) (.reg 159)
  , .binop 162 .mul (.reg 158) (.reg 161) ]             -- marked q

def Cfg.classSecondShapeBody : List Instr :=
  [ .binop rShapeQ .mul (.reg 162) (.reg 144)
  , .binop 163 .mul (.reg 160) (.reg rShapeRest)
  , .binop rShapeQ .add (.reg rShapeQ) (.reg 163)
  , .binop rShapeQE .mul (.reg 162) (.reg 145)
  , .binop rShapeQE .add (.reg rShapeQE) (.reg 160) ]

def Cfg.classTailBody : List Instr :=
  [ .binop 164 .eq (.reg 146) (.lit 0)
  , .binop 165 .add (.reg 146) (.reg 164)               -- qProd
  , .binop 166 .udiv (.reg rShapeRest) (.reg 165)
  , .binop rShapeTail .mul (.reg 162) (.reg 166)
  , .binop 167 .sub (.lit 1) (.reg 162)
  , .binop rShapeTail .add (.reg rShapeTail) (.reg 167) ]

/-- Exact arithmetic guard for the first decoded factor.  For an unmarked
prime the first factor is `n`; otherwise it is the first small prime power. -/
def Cfg.classFirstGuardBody : List Instr :=
  [ .binop 175 .mul (.reg 149) (.reg 132)
  , .binop 176 .mul (.reg 150) (.reg 152)
  , .binop 175 .add (.reg 175) (.reg 176)
  , .binop 168 .mul (.reg 175) (.reg rShapeRest)
  , .binop 169 .eq (.reg 168) (.reg 132) ]

/-- Exact arithmetic guard for the second decoded factor. -/
def Cfg.classSecondGuardBody : List Instr :=
  [ .binop 175 .mul (.reg 160) (.reg rShapeRest)
  , .binop 176 .mul (.reg 162) (.reg 165)
  , .binop 175 .add (.reg 175) (.reg 176)
  , .binop 175 .add (.reg 175) (.reg 157)
  , .binop 170 .mul (.reg 175) (.reg rShapeTail)
  , .binop 171 .eq (.reg 170) (.reg rShapeRest) ]

def Cfg.classGuardCommitBody : List Instr :=
  [ .binop 172 .mul (.reg 169) (.reg 171)
  , .binop 173 .sub (.lit 1) (.reg 172)
  , .binop 174 .mul (.reg 11) (.reg 173)
  , .binop rViol .add (.reg rViol) (.reg 174)
  , .binop rVShape .add (.reg rVShape) (.reg 174)
  , .binop rSeen .add (.reg rSeen) (.reg 11) ]

def Cfg.classDecodeBody : List Instr :=
  classNormalizeBody ++ classFirstShapeBody ++ classSecondFlagsBody ++
    classSecondShapeBody ++ classTailBody ++ classFirstGuardBody ++
    classSecondGuardBody ++ classGuardCommitBody

/-- Machine bit which is one exactly when `x` is zero. -/
def zeroBit (x : Nat) : Nat := if x = 0 then 1 else 0

/-- Complementary machine bit which is one exactly when `x` is nonzero. -/
def nonzeroBit (x : Nat) : Nat := 1 - zeroBit x

/-- Decode the empty-product sentinel `0` as the mathematical product `1`. -/
def nonzeroProduct (x : Nat) : Nat := x + zeroBit x

/-- Machine bit which is one exactly when `x = 1`. -/
def oneBit (x : Nat) : Nat := if x = 1 then 1 else 0

/-- Complementary machine bit which is one exactly when `x ≠ 1`. -/
def notOneBit (x : Nat) : Nat := 1 - oneBit x

def Cfg.classClearBody : List AInstr :=
  [ .store 131 0, .store 133 0, .store 134 0, .store 135 0
  , .store 136 0, .store 137 0, .store 138 0
  ]

def Cfg.classIndexBody (c : Cfg) : List AInstr :=
  lift c.classOffsetBody ++ lift classCandidateBody

def Cfg.classPostCandidateBody (c : Cfg) : List AInstr :=
  lift c.classPlaneBody ++ lift c.classSinkBody ++ classLoadBody ++
    lift classDecodeBody ++ classClearBody

def Cfg.classBody (c : Cfg) : List AInstr :=
  c.classIndexBody ++ c.classPostCandidateBody

private theorem wordSub_eq_sub {x y : Nat} (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hrew : x + (M - y) = M + (x - y) := by omega
  rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le x y) hx

/-- In the classification phase, the first two instructions recover the live
cell offset.  Keeping this proof at two instructions prevents the kernel from
normalizing the full classifier in one term. -/
theorem Cfg.classOffsetBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR)
    (hR : s.regs rR < M) :
    let out := arun k s (lift c.classOffsetBody)
    out.regs 130 = s.regs rR - c.markSteps ∧
      out.regs 131 = s.regs rR - c.markSteps ∧
      out.regs rR = s.regs rR ∧ out.regs rW = s.regs rW ∧
      out.regs 11 = 1 ∧ out.arr = s.arr := by
  have hTlt : c.markSteps < M := Nat.lt_of_le_of_lt hT hR
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTlt
  have hsub := wordSub_eq_sub hT hR
  have hsub5 :
      (s.regs 5 + (M - c.markSteps)) % M =
        s.regs 5 - c.markSteps := by
    simpa [rR] using hsub
  have hoff : s.regs rR - c.markSteps < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hR
  have hoff5 : s.regs 5 - c.markSteps < M := by simpa [rR] using hoff
  have hoffmod :
      (s.regs 5 - c.markSteps) % M = s.regs 5 - c.markSteps :=
    Nat.mod_eq_of_lt hoff5
  rw [arun_lift]
  simp [Cfg.classOffsetBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rR, rW, hphase, hTmod, hsub5, hoffmod]

/-- The retained candidate register is the window base plus the live offset. -/
theorem Cfg.classCandidateBody_run (k : Nat) (s : AState)
    (hsum : s.regs 131 + s.regs rW < M) :
    let out := arun k s (lift classCandidateBody)
    out.regs 132 = s.regs 131 + s.regs rW ∧
      out.regs 131 = s.regs 131 ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  have hsum6 : s.regs 131 + s.regs 6 < M := by simpa [rW] using hsum
  rw [arun_lift]
  simp [Cfg.classCandidateBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rW, Nat.mod_eq_of_lt hsum6]

/-- The three-instruction index prefix retains the exact candidate and the
live classification gate. -/
theorem Cfg.classIndexBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M) :
    let out := arun k s c.classIndexBody
    out.regs 132 = s.regs rR - c.markSteps + s.regs rW ∧
      out.regs 11 = 1 ∧ out.arr = s.arr := by
  let s1 := arun k s (lift c.classOffsetBody)
  have ho := Cfg.classOffsetBody_run c k s hphase hT hR
  dsimp only at ho
  have hsum1 : s1.regs 131 + s1.regs rW < M := by
    rw [ho.2.1, ho.2.2.2.1]
    exact hsum
  have hc := Cfg.classCandidateBody_run k s1 hsum1
  dsimp only at hc
  have hc11 :
      (arun k s1 (lift Cfg.classCandidateBody)).regs 11 = s1.regs 11 :=
    arun_frame k 11 _ (by decide) s1
  rw [Cfg.classIndexBody, arun_append]
  constructor
  · rw [hc.1, ho.2.1, ho.2.2.2.1]
  constructor
  · rw [hc11, ho.2.2.2.2.1]
  · rw [hc.2.2.2, ho.2.2.2.2.2]

/-- The load/decode/guard/clear suffix never overwrites the retained candidate
or the classification gate.  This proof examines only destination indices. -/
theorem Cfg.classPostCandidateBody_frame (c : Cfg) (k : Nat) (s : AState) :
    let out := arun k s c.classPostCandidateBody
    out.regs 132 = s.regs 132 ∧ out.regs 11 = s.regs 11 := by
  exact ⟨arun_frame k 132 _ (by rfl) s,
    arun_frame k 11 _ (by rfl) s⟩

/-- The complete classifier exposes the exact candidate consumed by the
verified log/lambda/psi arithmetic, and keeps its live gate equal to one. -/
theorem Cfg.classBody_candidate_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M) :
    let out := arun k s c.classBody
    out.regs 132 = s.regs rR - c.markSteps + s.regs rW ∧
      out.regs 11 = 1 := by
  let mid := arun k s c.classIndexBody
  have hi := Cfg.classIndexBody_run c k s hphase hT hR hsum
  have hp := Cfg.classPostCandidateBody_frame c k mid
  dsimp only at hi hp
  rw [Cfg.classBody, arun_append]
  constructor
  · rw [hp.1, hi.1]
  · rw [hp.2, hi.2.1]

/-- The live cell offset determines the six remaining plane addresses. -/
theorem Cfg.classPlaneBody_run (c : Cfg) (k : Nat) (s : AState)
    (h1 : s.regs 131 + c.segLen < M)
    (h2 : s.regs 131 + 2 * c.segLen < M)
    (h3 : s.regs 131 + 3 * c.segLen < M)
    (h4 : s.regs 131 + 4 * c.segLen < M)
    (h5 : s.regs 131 + 5 * c.segLen < M)
    (h6 : s.regs 131 + 6 * c.segLen < M) :
    let out := arun k s (lift c.classPlaneBody)
    out.regs 133 = s.regs 131 + c.segLen ∧
      out.regs 134 = s.regs 131 + 2 * c.segLen ∧
      out.regs 135 = s.regs 131 + 3 * c.segLen ∧
      out.regs 136 = s.regs 131 + 4 * c.segLen ∧
      out.regs 137 = s.regs 131 + 5 * c.segLen ∧
      out.regs 138 = s.regs 131 + 6 * c.segLen ∧
      out.regs 131 = s.regs 131 ∧ out.arr = s.arr := by
  have hl1 : c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h1
  have hl2 : 2 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h2
  have hl3 : 3 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h3
  have hl4 : 4 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h4
  have hl5 : 5 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h5
  have hl6 : 6 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h6
  rw [arun_lift]
  simp [Cfg.classPlaneBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5,
    Nat.mod_eq_of_lt h6, Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hl2,
    Nat.mod_eq_of_lt hl3, Nat.mod_eq_of_lt hl4, Nat.mod_eq_of_lt hl5,
    Nat.mod_eq_of_lt hl6]

/-- In the classification phase the sink shift is zero, so all seven live
plane addresses are preserved. -/
theorem Cfg.classSinkBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 0)
    (h131 : s.regs 131 < M) (h133 : s.regs 133 < M)
    (h134 : s.regs 134 < M) (h135 : s.regs 135 < M)
    (h136 : s.regs 136 < M) (h137 : s.regs 137 < M)
    (h138 : s.regs 138 < M) :
    let out := arun k s (lift c.classSinkBody)
    out.regs 130 = 0 ∧ out.regs 131 = s.regs 131 ∧
      out.regs 133 = s.regs 133 ∧ out.regs 134 = s.regs 134 ∧
      out.regs 135 = s.regs 135 ∧ out.regs 136 = s.regs 136 ∧
      out.regs 137 = s.regs 137 ∧ out.regs 138 = s.regs 138 ∧
      out.arr = s.arr := by
  rw [arun_lift]
  simp [Cfg.classSinkBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, hphase, Nat.mod_eq_of_lt h131, Nat.mod_eq_of_lt h133,
    Nat.mod_eq_of_lt h134, Nat.mod_eq_of_lt h135,
    Nat.mod_eq_of_lt h136, Nat.mod_eq_of_lt h137,
    Nat.mod_eq_of_lt h138]

/-- The seven loads read the all-product and two prime-power triples without
changing the live addresses or the array. -/
theorem Cfg.classLoadBody_run (k : Nat) (s : AState) :
    let out := arun k s Cfg.classLoadBody
    out.regs 140 = s.arr (s.regs 131) ∧
      out.regs 141 = s.arr (s.regs 133) ∧
      out.regs 142 = s.arr (s.regs 134) ∧
      out.regs 143 = s.arr (s.regs 135) ∧
      out.regs 144 = s.arr (s.regs 136) ∧
      out.regs 145 = s.arr (s.regs 137) ∧
      out.regs 146 = s.arr (s.regs 138) ∧
      out.regs 131 = s.regs 131 ∧ out.regs 133 = s.regs 133 ∧
      out.regs 134 = s.regs 134 ∧ out.regs 135 = s.regs 135 ∧
      out.regs 136 = s.regs 136 ∧ out.regs 137 = s.regs 137 ∧
      out.regs 138 = s.regs 138 ∧ out.arr = s.arr := by
  simp [Cfg.classLoadBody, arun, astep, AState.writeReg]

/-- Exactly the seven live plane addresses are the partiality obligations of
the classifier load stage. -/
theorem Cfg.classLoadBody_defined (len k : Nat) (s : AState)
    (h131 : s.regs 131 < len) (h133 : s.regs 133 < len)
    (h134 : s.regs 134 < len) (h135 : s.regs 135 < len)
    (h136 : s.regs 136 < len) (h137 : s.regs 137 < len)
    (h138 : s.regs 138 < len) :
    AllDefined len k s Cfg.classLoadBody := by
  simp [Cfg.classLoadBody, AllDefined, ADefined, astep, AState.writeReg,
    h131, h133, h134, h135, h136, h137, h138]


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
