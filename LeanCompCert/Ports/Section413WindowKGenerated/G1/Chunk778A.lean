import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk778A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483030962981597, 362483121531998609⟩, ⟨158456703688648235, 163214937779123977⟩, true⟩

def state01 : KState := ⟨⟨362485784439033796, 362485875032064419⟩, ⟨(-55723707517722294), (-50963605045244032)⟩, true⟩

def words00 : List Nat := [371285219523410450, 371285219581949741, 371285219721868419, 371285219862839841, 371285219989592135, 371285219992276341, 371285219925604382, 371285219955869075, 371285220054279480, 371285220065478137]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492648043263653, 362492738660749634⟩, ⟨(-589792584104232673), (-585030578636931711)⟩, true⟩

def words01 : List Nat := [371285220067485976, 371285220064024545, 371285220218138238, 371285220324993582, 371285220478798003, 371285220633650949, 371285220787561856, 371285220818329626, 371285220916787910, 371285221016686503]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488482373902635, 362488573015298425⟩, ⟨(-265590579887704612), (-260826713636827264)⟩, true⟩

def words02 : List Nat := [371285221250110286, 371285221280590614, 371285221309610893, 371285221339563387, 371285221378850807, 371285221381869551, 371285221506267034, 371285221641734901, 371285221776314877, 371285221822153832]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501547616405154, 362501638282144181⟩, ⟨(-1282554118036460846), (-1277788357032714546)⟩, true⟩

def words03 : List Nat := [371285221976349539, 371285222131984893, 371285222354737544, 371285222358373748, 371285222360452071, 371285222337767715, 371285222442448916, 371285222491336724, 371285222704049685, 371285222918042581]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481926934748878, 362482017624722056⟩, ⟨244765433699426047, 249533081213906009⟩, true⟩

def words04 : List Nat := [371285223133548138, 371285223136233862, 371285223191236156, 371285223254036054, 371285223366014569, 371285223368700490, 371285223260969864, 371285223096270138, 371285222930455963, 371285222930839127]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk778A
