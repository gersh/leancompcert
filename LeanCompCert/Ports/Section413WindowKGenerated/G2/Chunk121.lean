import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk121

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360453510061220970, 360453510872546269⟩, ⟨1549782596447494509, 1549789247449603435⟩, true⟩

def state01 : KState := ⟨⟨360597115039216832, 360597115851943962⟩, ⟨(-188902779816692763), (-188896111845332433)⟩, true⟩

def words00 : List Nat := [360581582044259736, 360581578236129467, 360581577889412080, 360581573446201515, 360581569003714354, 360581558689681530, 360581541618920830, 360581531319789287, 360581521022315802, 360581518782185451]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602855145302467, 360602855959442930⟩, ⟨(-258545456037300749), (-258538770943325753)⟩, true⟩

def words01 : List Nat := [360581518782318668, 360581514769161515, 360581513509743489, 360581519664026204, 360581524105107504, 360581528545480536, 360581528545615208, 360581527617176473, 360581524377512858, 360581526137568223]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360616594648155745, 360616595463696839⟩, ⟨(-425263365639325850), (-425256663562751986)⟩, true⟩

def words02 : List Nat := [360581526137689197, 360581528728746496, 360581528728880339, 360581528061371392, 360581527393946124, 360581525208416195, 360581530672606047, 360581536135923149, 360581537206035763, 360581540096162197]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360651799840079323, 360651800657026696⟩, ⟨(-853083790595225534), (-853077071453451158)⟩, true⟩

def words03 : List Nat := [360581542802301228, 360581545508036810, 360581549201822360, 360581549201971178, 360581546164600227, 360581537262177057, 360581528361192530, 360581524927989103, 360581530716884776, 360581536504860199]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360625825942312422, 360625826760679230⟩, ⟨(-538265676358753914), (-538258939978175226)⟩, true⟩

def words04 : List Nat := [360581537809437801, 360581537809587383, 360581543417465547, 360581549585995770, 360581550850591976, 360581550850740955, 360581545397698476, 360581536559679392, 360581527723086982, 360581529259240816]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360439340562621885, 360439341382395015⟩, ⟨1728835377951187354, 1728842131425772844⟩, true⟩

def words05 : List Nat := [360581536225547717, 360581543190739034, 360581546775528537, 360581546820918484, 360581546821045127, 360581540331200202, 360581534069473151, 360581534069622324, 360581527592572350, 360581515899782003]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360731901178187001, 360731901999368594⟩, ⟨(-1829983358762103705), (-1829976588153420149)⟩, true⟩

def words06 : List Nat := [360581504208880977, 360581499231608694, 360581502858533604, 360581508026645490, 360581508026783112, 360581510614899889, 360581517109976709, 360581523604031403, 360581534161239375, 360581546515993899]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560708439859022, 360560709262464753⟩, ⟨254348396339696799, 254355184287010167⟩, true⟩

def words07 : List Nat := [360581555501049652, 360581564484645786, 360581570794178014, 360581580523844597, 360581588412856669, 360581596300597103, 360581598489445110, 360581598489594503, 360581593997022644, 360581592282521158]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360461724878609566, 360461725702622799⟩, ⟨1460163766992439832, 1460170572090287164⟩, true⟩

def words08 : List Nat := [360581590715349319, 360581590715498764, 360581584183835289, 360581573655775498, 360581563129419555, 360581550905481726, 360581542030203577, 360581532971890811, 360581523915047582, 360581509998938656]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360686122075774882, 360686122901200339⟩, ⟨(-1276359819308018766), (-1276352996988098654)⟩, true⟩

def words09 : List Nat := [360581500173426533, 360581494757228959, 360581489341876473, 360581490786783786, 360581490786923024, 360581487517538653, 360581487649676993, 360581495226770621, 360581503802931540, 360581512377719633]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk121
