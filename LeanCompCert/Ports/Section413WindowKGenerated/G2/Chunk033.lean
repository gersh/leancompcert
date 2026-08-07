import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk033

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359979807465717581, 359979807518297875⟩, ⟨1951604237937682550, 1951604355814469264⟩, true⟩

def state01 : KState := ⟨⟨360428868632046710, 360428868684962919⟩, ⟨467511061847415154, 467511180834446890⟩, true⟩

def words00 : List Nat := [360571023621269716, 360570934357525745, 360570828917194467, 360570675500700032, 360570522177038281, 360570345641597494, 360570231085361720, 360570206066377642, 360570181062511436, 360570110733553387]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360627056432230905, 360627056485486237⟩, ⟨(-192157352624480591), (-192157232513263289)⟩, true⟩

def words01 : List Nat := [360570068075157052, 360569965147635750, 360569862282239379, 360569848680118290, 360569745675381293, 360569559545090009, 360569373527020087, 360569231818056256, 360569177800957118, 360569195229083569]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360623735277273156, 360623735330871200⟩, ⟨(-183305034127623819), (-183304912876886537)⟩, true⟩

def words02 : List Nat := [360569195229115921, 360569156681576508, 360569159511828677, 360569205258386265, 360569205258417018, 360569182071907922, 360569070051959622, 360568913415291035, 360568756872719848, 360568705336011733]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨359785373684881187, 359785373738819554⟩, ⟨2614564005735283218, 2614564128121029432⟩, true⟩

def words03 : List Nat := [360568810185960103, 360568914972999714, 360568946083396713, 360568946083432808, 360568888645573666, 360568769877538490, 360568651180675553, 360568575686524439, 360568411812493179, 360568177369993515]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551473748459627, 360551473802740023⟩, ⟨51815485360119634, 51815608889964534⟩, true⟩

def words04 : List Nat := [360567943067828704, 360567729931781032, 360567564486170415, 360567486871236173, 360567409302705345, 360567251373488989, 360567101773323958, 360567039871261329, 360566978006155523, 360566941148677326]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360421686201693517, 360421686256320463⟩, ⟨486240161611059601, 486240286303600093⟩, true⟩

def words05 : List Nat := [360566936532969319, 360566887780538932, 360566839057182104, 360566794109364989, 360566794109395697, 360566736202350877, 360566678329801663, 360566573810879664, 360566443709777632, 360566400627244154]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360283415196976075, 360283415251946682⟩, ⟨951953329818793053, 951953455667765567⟩, true⟩

def words06 : List Nat := [360566401429362318, 360566401429398765, 360566390988520255, 360566319296992998, 360566247648069985, 360566153272345548, 360566138203851483, 360566071386567726, 360566004608945970, 360565894022174506]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360972453139897838, 360972453195213889⟩, ⟨(-1372895553788071123), (-1372895426773220837)⟩, true⟩

def words07 : List Nat := [360565812901798743, 360565815576574556, 360565904622762176, 360566000889763659, 360566022525185469, 360566044147796451, 360566074511760726, 360566150908441936, 360566271116248853, 360566391252956208]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360753648964653220, 360753649020319129⟩, ⟨(-635080309728706095), (-635080181529577937)⟩, true⟩

def words08 : List Nat := [360566439710651694, 360566463503091693, 360566512570622767, 360566561609173468, 360566588408099378, 360566588408136104, 360566529697000310, 360566427854189153, 360566326071472259, 360566364979761896]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359929514696142912, 359929514752155511⟩, ⟨2164848130347267887, 2164848259723441967⟩, true⟩

def words09 : List Nat := [360566505528764641, 360566645994927897, 360566725748241028, 360566725748277829, 360566720197067810, 360566646596043179, 360566573038341010, 360566540166048577, 360566422154212976, 360566234828544759]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk033
