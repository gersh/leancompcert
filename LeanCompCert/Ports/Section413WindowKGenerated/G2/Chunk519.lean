import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598241187801568, 360598258137372299⟩, ⟨(-845347965012324023), (-844753576555771549)⟩, true⟩

def state01 : KState := ⟨⟨360577578255357767, 360577595211690132⟩, ⟨227041265169421303, 227636004588460237⟩, true⟩

def words00 : List Nat := [360581982169583842, 360581982170302261, 360581982080673842, 360581981776675256, 360581981472581583, 360581980911523831, 360581980631337989, 360581980676970404, 360581980677617779, 360581980416941307]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594460779877993, 360594477743000856⟩, ⟨(-649460729267249810), (-648865637320078396)⟩, true⟩

def words01 : List Nat := [360581980333047963, 360581980239212806, 360581980421032855, 360581980440298174, 360581980440960691, 360581980142212166, 360581979843337511, 360581980088830071, 360581980330130917, 360581980571580428]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360609456946060093, 360609473916027012⟩, ⟨(-1428300467323194650), (-1427705019998424280)⟩, true⟩

def words02 : List Nat := [360581980623353222, 360581980624075305, 360581980806008791, 360581981040867445, 360581981094766707, 360581981159213736, 360581981159855285, 360581980996683450, 360581981039790659, 360581981570029469]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557447160629501, 360557464137374485⟩, ⟨1272874301194702239, 1273470100538170765⟩, true⟩

def words03 : List Nat := [360581982156004004, 360581982742089819, 360581983044356606, 360581983175063382, 360581983175669622, 360581983006193920, 360581982956745825, 360581982957464819, 360581982708413541, 360581982237115305]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599596249594066, 360599613233124880⟩, ⟨(-916491319338812229), (-915895167506164365)⟩, true⟩

def words04 : List Nat := [360581981765659065, 360581981844096938, 360581982310813411, 360581982777649974, 360581982926897562, 360581982927618186, 360581982920419986, 360581982794461492, 360581982911542202, 360581983251651835]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590853566620605, 360590870556994723⟩, ⟨(-462275037668391915), (-461678530291448011)⟩, true⟩

def words05 : List Nat := [360581983405809461, 360581983560041686, 360581983770231018, 360581984265135779, 360581984667413979, 360581985069794653, 360581985228414682, 360581985229134008, 360581985288078099, 360581985459897065]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560056808792152, 360560073805949474⟩, ⟨1137958620791435394, 1138555480658560352⟩, true⟩

def words06 : List Nat := [360581985474346631, 360581985475065964, 360581985119965860, 360581984579308360, 360581984038550766, 360581983314312797, 360581982773450425, 360581982516141454, 360581982258752497, 360581981742848812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614756589436825, 360614773593382086⟩, ⟨(-1705071565808975117), (-1704474353140435109)⟩, true⟩

def words07 : List Nat := [360581981321888899, 360581981270826660, 360581981537359977, 360581981751832180, 360581981752519238, 360581981582047711, 360581981609880112, 360581981996349614, 360581982627781672, 360581983259353491]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624946751792744, 360624963762601640⟩, ⟨(-2234859400875050598), (-2234261831401649340)⟩, true⟩

def words08 : List Nat := [360581983705253186, 360581984251645994, 360581985079411225, 360581985907364706, 360581986562298072, 360581987350968421, 360581987879506179, 360581988408098860, 360581988923708181, 360581989751111159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575624272573135, 360575641290157105⟩, ⟨329804278273138664, 330402200017120654⟩, true⟩

def words09 : List Nat := [360581990947635411, 360581992144251725, 360581993131899620, 360581993750418021, 360581994276475638, 360581994802717446, 360581995235578491, 360581995299420725, 360581995300061965, 360581995178618973]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519
