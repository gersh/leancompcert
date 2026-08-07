import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk509

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496631270976770, 362496668760835717⟩, ⟨(-592830664831325728), (-591541491100314660)⟩, true⟩

def state01 : KState := ⟨⟨362485014982226987, 362485052487436094⟩, ⟨(-1564870673508142), (-274915543059744)⟩, true⟩

def words00 : List Nat := [371285047554729116, 371285047556431162, 371285047453194743, 371285047582136760, 371285047828850154, 371285047830550981, 371285047563453759, 371285047276536204, 371285047085466038, 371285047087511853]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464014996131546, 362464052516684684⟩, ⟨1067687259622839951, 1068977995996234463⟩, true⟩

def words01 : List Nat := [371285047248905486, 371285047410988590, 371285047570719658, 371285047572420813, 371285047218325717, 371285046889718026, 371285046560262084, 371285046545753394, 371285046210545655, 371285045800188146]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485907967841961, 362485945503624422⟩, ⟨(-47194130965942610), (-45902619037809624)⟩, true⟩

def words02 : List Nat := [371285045389076998, 371285045234664175, 371285045012146579, 371285045094678881, 371285045096020699, 371285045050045608, 371285044490028058, 371285044270486394, 371285044213435098, 371285044232904472]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475495551296263, 362475533102589005⟩, ⟨483239750475693247, 484532052421805827⟩, true⟩

def words03 : List Nat := [371285044250230604, 371285044268139045, 371285044562237939, 371285044711961842, 371285044938022917, 371285045164740425, 371285045391232145, 371285045392934152, 371285045106065260, 371285044921442987]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362451244829828484, 362451282396284245⟩, ⟨1718710404813396443, 1720003479242563519⟩, true⟩

def words04 : List Nat := [371285044737908876, 371285044739610968, 371285044229724323, 371285043720878072, 371285043211378709, 371285042754056028, 371285042155026435, 371285041812684249, 371285041469814174, 371285041051421489]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479238032443090, 362479275614336811⟩, ⟨292291955985139511, 293585817052359095⟩, true⟩

def words05 : List Nat := [371285040390006095, 371285040114134391, 371285039837385362, 371285039641723424, 371285038990810165, 371285038294970200, 371285037598481689, 371285037287308586, 371285036828572736, 371285036717497180]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458570463418628, 362458608060648474⟩, ⟨1345530205247403011, 1346824847923472953⟩, true⟩

def words06 : List Nat := [371285036605721499, 371285036494861651, 371285035923861960, 371285035473815077, 371285035022962601, 371285034691047948, 371285033964966885, 371285033160183948, 371285032354723472, 371285031934455096]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463634651985639, 362463672264543827⟩, ⟨1087490724722502595, 1088786148760943599⟩, true⟩

def words07 : List Nat := [371285031417201276, 371285031284997016, 371285031152245680, 371285031014471557, 371285030660319110, 371285030421325432, 371285030221433677, 371285030223137330, 371285029804944012, 371285029387901241]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478997604241783, 362479035232063373⟩, ⟨304210432230780644, 305506634476038102⟩, true⟩

def words08 : List Nat := [371285028970154541, 371285028712453098, 371285028306460673, 371285028144933052, 371285027982888938, 371285027692813241, 371285027111517295, 371285026857733932, 371285026731269965, 371285026733033682]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478377105126419, 362478414748492824⟩, ⟨335892082001441433, 337189076952466119⟩, true⟩

def words09 : List Nat := [371285026616808911, 371285026471502566, 371285026562321274, 371285026609734127, 371285026677943058, 371285026746779857, 371285026808917331, 371285026810622359, 371285026426528380, 371285026299021304]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk509
