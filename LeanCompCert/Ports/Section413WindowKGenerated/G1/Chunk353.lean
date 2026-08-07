import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk353

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362529767139027229, 362529784640973635⟩, ⟨(-1581649129340810774), (-1581231583844796226)⟩, true⟩

def state01 : KState := ⟨⟨362493252364716907, 362493269877019626⟩, ⟨(-292564461162963741), (-292146550036316119)⟩, true⟩

def words00 : List Nat := [371284992859009091, 371284993080585006, 371284993951522139, 371284994823012421, 371284995778944280, 371284995780090902, 371284995775304029, 371284995775353112, 371284996113312412, 371284996348939529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473403863751132, 362473421386370811⟩, ⟨408518864595939226, 408937140067723138⟩, true⟩

def words01 : List Nat := [371284997385835445, 371284998423153488, 371284999430015279, 371284999431162353, 371284999369604933, 371284999337417830, 371285000072710444, 371285000073857607, 371284999774609696, 371284999448094133]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485294164892312, 362485311697796933⟩, ⟨(-11431225204011303), (-11012586416436081)⟩, true⟩

def words02 : List Nat := [371284999121087950, 371284998945016158, 371284998924724930, 371284999316116334, 371284999563435765, 371284999564586122, 371284999233297385, 371284999469305723, 371284999990229196, 371285000000239082]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494267626641986, 362494285169986146⟩, ⟨(-328471394675091717), (-328052387006646201)⟩, true⟩

def words03 : List Nat := [371285000005069315, 371285000010284484, 371285000698490783, 371285001092665309, 371285001627217824, 371285002162210322, 371285002691985353, 371285002693132875, 371285002418518211, 371285002682591714]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474434112594836, 362474451666174180⟩, ⟨372547755484355678, 372967124916801674⟩, true⟩

def words04 : List Nat := [371285003578726065, 371285003579874353, 371285003555985078, 371285003188143632, 371285002819868670, 371285002698079319, 371285002265832998, 371285002316130794, 371285002361567025, 371285002362777202]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362504513885203598, 362504531449172667⟩, ⟨(-690914280373868004), (-690494543612842002)⟩, true⟩

def words05 : List Nat := [371285002091573521, 371285002119438193, 371285002946704107, 371285003062524608, 371285003063412967, 371285003053658751, 371285003363741468, 371285003365006483, 371285003887234611, 371285004440784532]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477867956425826, 362477885530751469⟩, ⟨251330830276002450, 251750933299116540⟩, true⟩

def words06 : List Nat := [371285004998605301, 371285004999753780, 371285004783027891, 371285005075424043, 371285005401761748, 371285005402910405, 371285004664007707, 371285003921038103, 371285003177633807, 371285003170935216]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463915107478238, 362463932692154861⟩, ⟨744934863141488589, 745355332330059007⟩, true⟩

def words07 : List Nat := [371285003008125858, 371285003046985445, 371285003074752063, 371285003075902593, 371285002249168711, 371285001675120800, 371285001100488648, 371285001023672962, 371285000424058586, 371284999829869109]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484254213368177, 362484271808315159⟩, ⟨25345535547705274, 25766368155836976⟩, true⟩

def words08 : List Nat := [371284999438556078, 371284999439821583, 371284999657093659, 371285000067901084, 371285000267290568, 371285000268445268, 371284999705694150, 371284999546786878, 371284999876302111, 371284999877491645]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486869132521966, 362486886737968563⟩, ⟨(-67116187187344206), (-66694982946314640)⟩, true⟩

def words09 : List Nat := [371284999857778984, 371284999799760846, 371285000480148923, 371285000889650421, 371285001543802815, 371285002198347705, 371285002775828775, 371285002776986190, 371285002697467419, 371285002752122223]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk353
