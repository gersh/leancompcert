import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552594567507931, 360552598713417579⟩, ⟨796226194862683399, 796300231885982503⟩, true⟩

def state01 : KState := ⟨⟨360568909662525922, 360568913811695963⟩, ⟨365246653575385951, 365320776689339235⟩, true⟩

def words00 : List Nat := [360582760458779685, 360582759789384617, 360582758290849133, 360582755901326989, 360582753511923039, 360582750753599330, 360582748792752143, 360582748262732608, 360582747732715633, 360582746480256711]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612147874109611, 360612152026554826⟩, ⟨(-777204691262294627), (-777130481635203751)⟩, true⟩

def words01 : List Nat := [360582745956797343, 360582744707765310, 360582743458726521, 360582743174350512, 360582741980128019, 360582739533432941, 360582737086855464, 360582736435558911, 360582737549223000, 360582738662880658]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574055636309608, 360574059792053499⟩, ⟨229305332423723129, 229379629218431263⟩, true⟩

def words02 : List Nat := [360582739055133401, 360582739253680925, 360582740880869260, 360582742508039120, 360582743094337026, 360582743094683647, 360582742711752442, 360582741406074056, 360582740100430287, 360582738552145003]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360492371765039296, 360492375924050734⟩, ⟨2388827320379353569, 2388901703552125227⟩, true⟩

def words03 : List Nat := [360582739323879826, 360582740423958900, 360582740424273060, 360582740409443236, 360582738968622258, 360582736655189815, 360582734341831169, 360582733456398849, 360582731145279425, 360582727728269801]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613468217341176, 360613472379628375⟩, ⟨(-813642788665587542), (-813568318865981844)⟩, true⟩

def words04 : List Nat := [360582724311440528, 360582721949565897, 360582720474317258, 360582719826985017, 360582719179672766, 360582717179746591, 360582715224769324, 360582714225422506, 360582713652657290, 360582714815874038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264A
