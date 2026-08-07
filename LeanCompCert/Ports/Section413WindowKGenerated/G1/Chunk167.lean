import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk167

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362558276901419175, 362558280576268872⟩, ⟨(-1220788077798326873), (-1220746566051546663)⟩, true⟩

def state01 : KState := ⟨⟨362490398424817218, 362490402104277405⟩, ⟨(-86778565341729220), (-86736976576323246)⟩, true⟩

def words00 : List Nat := [371285190699545466, 371285192077740448, 371285197041111195, 371285202004163957, 371285207622578552, 371285208470079421, 371285209303060245, 371285210136108546, 371285211380980352, 371285211692179008]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469353002242162, 362469356686306753⟩, ⟨265143855491859816, 265185521220264594⟩, true⟩

def words01 : List Nat := [371285214208256965, 371285216724244043, 371285219239062395, 371285219239573296, 371285217628940415, 371285217069254390, 371285218948494320, 371285218949007695, 371285218012429137, 371285217064370166]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496780165638975, 362496783854278433⟩, ⟨(-193576807647278510), (-193535065403690598)⟩, true⟩

def words02 : List Nat := [371285217673327214, 371285217673894863, 371285218741355832, 371285220016264621, 371285220514088234, 371285220514599403, 371285216255060340, 371285214882457287, 371285215708767049, 371285216400724929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468622696430228, 362468626389723674⟩, ⟨277743869269591674, 277785689397819816⟩, true⟩

def words03 : List Nat := [371285216481943305, 371285216563311842, 371285219200615161, 371285220058423396, 371285221970057601, 371285223881665416, 371285225069547518, 371285225070059090, 371285221507639923, 371285220516927845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477474380554791, 362477478078404527⟩, ⟨129683267585583659, 129725164009628353⟩, true⟩

def words04 : List Nat := [371285222100988314, 371285222101503354, 371285221514982587, 371285220918430858, 371285220321738991, 371285220115682688, 371285219713576898, 371285221295033385, 371285222863785208, 371285222864315550]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362526088452890255, 362526092155376804⟩, ⟨(-685031411713576251), (-684989437599397951)⟩, true⟩

def words05 : List Nat := [371285223419520204, 371285224437215383, 371285227252124202, 371285227252636150, 371285225326404264, 371285222892566386, 371285220458817758, 371285220344197454, 371285221663294238, 371285224102301248]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491287758550883, 362491291465656143⟩, ⟨(-101701776123584355), (-101659724576588503)⟩, true⟩

def words06 : List Nat := [371285226114424109, 371285226114938029, 371285227735661448, 371285230325003293, 371285233110486462, 371285233110998858, 371285231746154215, 371285230115600256, 371285229465989337, 371285229828033069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362405035707643477, 362405039419363557⟩, ⟨1345512555132074523, 1345554684093532403⟩, true⟩

def words07 : List Nat := [371285233075447974, 371285236322687891, 371285239555699457, 371285239556212229, 371285238059134916, 371285236492814035, 371285235926636257, 371285235927149081, 371285232200489820, 371285227421991301]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362500982840061372, 362500986556370346⟩, ⟨(-264925047176979283), (-264882841190019515)⟩, true⟩

def words08 : List Nat := [371285222643840132, 371285220702724405, 371285216992309325, 371285215598005332, 371285214203705304, 371285212193846190, 371285208342462136, 371285208037206698, 371285210329442274, 371285211269538709]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483477873134512, 362483481594136374⟩, ⟨29099384304167212, 29141669107034248⟩, true⟩

def words09 : List Nat := [371285212026003561, 371285212782555263, 371285215016840426, 371285215499595416, 371285217029557044, 371285218559532956, 371285219436979750, 371285219437493743, 371285216319901202, 371285216217297507]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk167
