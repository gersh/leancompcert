import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk222

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362509461325086753, 362509467983138120⟩, ⟨(-564063684250099823), (-563963731277069655)⟩, true⟩

def state01 : KState := ⟨⟨362496718498762464, 362496725163000786⟩, ⟨(-280960318151774187), (-280860227795846335)⟩, true⟩

def words00 : List Nat := [371284068338211166, 371284069261653222, 371284070193554559, 371284071125610837, 371284072672336844, 371284073211992448, 371284075426380116, 371284077640859255, 371284079496915087, 371284080066976481]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362531239646214240, 362531246316735915⟩, ⟨(-1047913043693758817), (-1047812813752585633)⟩, true⟩

def words01 : List Nat := [371284081120592176, 371284082174461827, 371284084808964017, 371284085279066795, 371284085419705465, 371284085560552983, 371284087045571658, 371284087900894799, 371284090023709325, 371284092146637694]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498170911499945, 362498177588293741⟩, ⟨(-313128169862081393), (-313027800522713311)⟩, true⟩

def words02 : List Nat := [371284094243201702, 371284094243897225, 371284095577019097, 371284097108700240, 371284098693839183, 371284098694534489, 371284097583757497, 371284096469989374, 371284096264928257, 371284096899142434]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362429745334287138, 362429752017354132⟩, ⟨1208460048497934650, 1208560557322429400⟩, true⟩

def words03 : List Nat := [371284098153518861, 371284099408079606, 371284100653168573, 371284100653864067, 371284099204728557, 371284098369860813, 371284098219108047, 371284098219803710, 371284096211775864, 371284093769032299]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468116783374180, 362468123472670535⟩, ⟨354944099885931897, 355044747283040783⟩, true⟩

def words04 : List Nat := [371284091326191428, 371284090292230124, 371284088535680519, 371284087484130777, 371284086432466024, 371284085052062344, 371284082040643091, 371284081049443840, 371284080539243122, 371284080539964155]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362451943978879115, 362451950674516689⟩, ⟨714811137512937342, 714911926034228672⟩, true⟩

def words05 : List Nat := [371284079823345622, 371284079099137934, 371284078374732566, 371284077535520903, 371284075693205945, 371284074464618208, 371284073235899322, 371284072015244982, 371284068555226519, 371284067113242396]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362414514457315425, 362414521159153528⟩, ⟨1548253213369421070, 1548354139946620394⟩, true⟩

def words06 : List Nat := [371284066103935358, 371284066104631804, 371284063851082713, 371284061442393875, 371284059033643837, 371284057075200335, 371284054106173903, 371284051961082871, 371284049815957539, 371284047613574122]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362532765661016871, 362532772369156684⟩, ⟨(-1085768702841467208), (-1085667635893967810)⟩, true⟩

def words07 : List Nat := [371284044492209478, 371284043386683939, 371284043189725474, 371284043190435016, 371284042759598878, 371284041720835295, 371284041656927558, 371284041830801801, 371284044018462892, 371284046206242364]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362517136117885982, 362517142832328005⟩, ⟨(-737570716066758179), (-737469508673481671)⟩, true⟩

def words08 : List Nat := [371284048011751557, 371284048012452040, 371284049805745480, 371284051709714886, 371284054224525743, 371284054954450896, 371284055287314381, 371284055620401329, 371284057613557848, 371284059098593607]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473151583875704, 362473158304581589⟩, ⟨243326311283527004, 243427658331165878⟩, true⟩

def words09 : List Nat := [371284062595289156, 371284066091947163, 371284069596657917, 371284070748483800, 371284071930296502, 371284073112341337, 371284075311242914, 371284075311940671, 371284074831825006, 371284074343071776]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk222
