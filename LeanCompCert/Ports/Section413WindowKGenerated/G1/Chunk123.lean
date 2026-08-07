import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk123

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362526542927084876, 362526544867421646⟩, ⟨(-516311946379755063), (-516295795656574279)⟩, true⟩

def state01 : KState := ⟨⟨362474349190834879, 362474351134429434⟩, ⟨126154622621255479, 126170813432434309⟩, true⟩

def words00 : List Nat := [371284582999336896, 371284584209531892, 371284585318919261, 371284586428251128, 371284588168447586, 371284588168857096, 371284592427388677, 371284597220350519, 371284600590868926, 371284600591247666]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362553179415298843, 362553181362214258⟩, ⟨(-844725417320524915), (-844709185613392273)⟩, true⟩

def words01 : List Nat := [371284603214554994, 371284606670041143, 371284612896488089, 371284612896854430, 371284611886970398, 371284609721087349, 371284611297790690, 371284611738549137, 371284617304514596, 371284622869753144]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467073780356803, 362467075730578039⟩, ⟨216302427208623152, 216318699660461368⟩, true⟩

def words02 : List Nat := [371284627835543380, 371284627835909934, 371284629133539557, 371284633058043987, 371284636985155930, 371284636985522554, 371284632171510188, 371284625873351546, 371284619825830700, 371284619826252043]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362403522158977685, 362403524112497293⟩, ⟨1000380056052216342, 1000396369190232768⟩, true⟩

def words03 : List Nat := [371284618403740272, 371284618384120963, 371284618374228579, 371284618374601588, 371284612936553574, 371284609525356528, 371284606694990246, 371284606695357419, 371284600080092238, 371284593510324703]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468547230973734, 362468549187785526⟩, ⟨197602356922827794, 197618710702618768⟩, true⟩

def words04 : List Nat := [371284586941467828, 371284581282034843, 371284573685941613, 371284572625157278, 371284571564428114, 371284569374162675, 371284558469518277, 371284554097548006, 371284550702439383, 371284550702822176]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362434569435543182, 362434571395700957⟩, ⟨617494725656336993, 617511120776100457⟩, true⟩

def words05 : List Nat := [371284549407533208, 371284547552597650, 371284547247948771, 371284547248353402, 371284546336207142, 371284545584783138, 371284544833363509, 371284543997002272, 371284535884342832, 371284531842365691]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362423449159131503, 362423451122570530⟩, ⟨755259273051384167, 755275708744502899⟩, true⟩

def words06 : List Nat := [371284529060741936, 371284529061115713, 371284524905597466, 371284520694925279, 371284516484795085, 371284514284553873, 371284508905888599, 371284508943322223, 371284508943603148, 371284508172590296]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362583643437402717, 362583645404164016⟩, ⟨(-1227156957817899574), (-1227140481011374352)⟩, true⟩

def words07 : List Nat := [371284503821586569, 371284504406171753, 371284511490847579, 371284511738319774, 371284511738609812, 371284510015697463, 371284513068030302, 371284514578638369, 371284522586225275, 371284530592677757]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494296549035161, 362494298519126681⟩, ⟨(-120885592142844934), (-120869074091393524)⟩, true⟩

def words08 : List Nat := [371284538620321872, 371284539328889879, 371284541149471023, 371284542969952344, 371284546792266002, 371284546792636801, 371284544806618332, 371284542845803100, 371284543145488275, 371284543933210178]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362362991025262407, 362362992998675029⟩, ⟨1507157512012242046, 1507174071229166410⟩, true⟩

def words09 : List Nat := [371284551205625810, 371284558477020004, 371284564952882052, 371284564953250885, 371284562782550904, 371284561450623700, 371284560118732253, 371284558928172947, 371284549097233590, 371284539294741898]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk123
