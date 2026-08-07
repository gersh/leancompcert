import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk262

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362447466572368332, 362447475976337645⟩, ⟨993291385027146488, 993457952886032498⟩, true⟩

def state01 : KState := ⟨⟨362473754677002529, 362473764088422134⟩, ⟨304443781285681597, 304610544378903563⟩, true⟩

def words00 : List Nat := [371285392772183240, 371285391734717426, 371285390194853721, 371285390109918638, 371285390024739966, 371285389718624465, 371285387473331216, 371285386500834899, 371285386008370709, 371285386009230181]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362460260950031439, 362460270369000146⟩, ⟨658227567207239913, 658394528200570001⟩, true⟩

def words01 : List Nat := [371285385566453126, 371285385119155058, 371285384970877901, 371285384971795281, 371285384676584631, 371285384431612607, 371285384186378210, 371285383921631946, 371285381719601114, 371285380762905584]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362461718330338317, 362461727756721459⟩, ⟨620079409320295939, 620246564758039765⟩, true⟩

def words02 : List Nat := [371285379805828283, 371285379804367499, 371285378596098931, 371285377384180793, 371285376172021732, 371285375398875944, 371285374222255474, 371285374360321374, 371285374360953980, 371285374213631793]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362515215889767383, 362515225323674727⟩, ⟨(-783441054267298470), (-783273701431732018)⟩, true⟩

def words03 : List Nat := [371285373318744838, 371285373325762083, 371285374451925876, 371285374452761280, 371285374200630310, 371285373559895575, 371285373727641632, 371285373814809928, 371285374953009653, 371285376091502488]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475349928130758, 362475359369553326⟩, ⟨262626069873756716, 262793619946478166⟩, true⟩

def words04 : List Nat := [371285377225093224, 371285377225924949, 371285376426153050, 371285375924947848, 371285375423370780, 371285375192509361, 371285373664998561, 371285372145263632, 371285370625297657, 371285370555075097]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362433094665805547, 362433104114705100⟩, ⟨1372248507497514031, 1372416253879757199⟩, true⟩

def words05 : List Nat := [371285371242058246, 371285372310653736, 371285373390072888, 371285373390904894, 371285372538416739, 371285371871185327, 371285371203578467, 371285370703170963, 371285368718438841, 371285366729095038]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490805482677622, 362490814939023884⟩, ⟨(-143428274378082737), (-143260332407315275)⟩, true⟩

def words06 : List Nat := [371285364739537488, 371285364198618224, 371285363108089712, 371285363287511847, 371285363288157976, 371285363055679018, 371285361272177007, 371285360936930026, 371285361556646453, 371285361765090372]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485665703432585, 362485675167390626⟩, ⟨(-8369340229470486), (-8201198259299472)⟩, true⟩

def words07 : List Nat := [371285361765730490, 371285361719263299, 371285362300275707, 371285362356519080, 371285362852071686, 371285363347896350, 371285363815979933, 371285363816827189, 371285363096394343, 371285363109315998]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475158119982968, 362475167591359212⟩, ⟨267860832317001162, 268029169276113240⟩, true⟩

def words08 : List Nat := [371285364204216924, 371285364205052236, 371285363832090543, 371285363454827883, 371285363077293608, 371285362765978780, 371285362213392492, 371285362526982461, 371285362690121180, 371285362690989342]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362511545839951915, 362511555318860059⟩, ⟨(-688837653607392542), (-688669118596166350)⟩, true⟩

def words09 : List Nat := [371285363119854847, 371285363936875238, 371285366197891462, 371285366533078674, 371285366650055269, 371285366767291020, 371285368328332627, 371285369184091209, 371285370180341953, 371285371176865604]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk262
