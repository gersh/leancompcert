import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk000

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨0, 0⟩, ⟨0, 0⟩, true⟩

def state01 : KState := ⟨⟨333134920634920592, 333134920634920681⟩, ⟨520833333333333000, 520833333333333662⟩, true⟩

def words00 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 0 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 0 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨387752884656909128, 387752884656909723⟩, ⟨(-411078042328046752), (-411078042328037852)⟩, true⟩

def words01 : List Nat := [0, 0, 0, 0, 0, 371248586482961761, 367989730857378245, 366229844804191608, 367198982540507755, 368177739784146016]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 0 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨372113627109386478, 372113627109388047⟩, ⟨(-316202050264567032), (-316202050264533462)⟩, true⟩

def words02 : List Nat := [368177739784146095, 367403558057583492, 366381039915500203, 366314587836480282, 366253451923781944, 365812403388983498, 364971587183584039, 363529453617194608, 362186777538142374, 361913560971822452]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 0 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨327745280506795172, 327745280506798318⟩, ⟨1328331266534346499, 1328331266534436413⟩, true⟩

def words03 : List Nat := [362857696813183048, 363744612300521823, 363905767724391811, 363905767724391965, 363765375109012600, 363092084515769298, 362455188008647227, 362277247698803516, 361805056571783651, 360953562170159229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 0 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨366571244573754199, 366571244573759589⟩, ⟨(-316162210348748753), (-316162210348557325)⟩, true⟩

def words04 : List Nat := [360143604080809145, 359758503897341674, 360135782796126936, 360496293743855122, 360496293743855339, 360430646060545896, 360184007481746676, 360220995382972243, 360248000366788190, 360371985547317289]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 0 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨355778861085250260, 355778861085258502⟩, ⟨261853771226181739, 261853771226530963⟩, true⟩

def words05 : List Nat := [360371985547317524, 360230096407747716, 360212443426360242, 360495352469338455, 360559289117559072, 360620982374614112, 360620982374614400, 360498290984077008, 360217060597572222, 360143090605700685]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 0 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360403211057837335, 360403211057849058⟩, ⟨(-90752962871565532), (-90752962870989058)⟩, true⟩

def words06 : List Nat := [360196161088837769, 360196161088838107, 360157992653898769, 359930354780170361, 359709721148710495, 359370158209909619, 359220449786551176, 359229002265760481, 359229002265760839, 359125000313187241]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 0 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨373572652603818172, 373572652603834079⟩, ⟨(-1073698210265553746), (-1073698210264662138)⟩, true⟩

def words07 : List Nat := [359289336078586272, 359449169494248463, 359748451775791798, 359931976246611854, 359961600532944971, 359990455357295455, 359990455357295832, 359981536018204575, 360151424975525318, 360317119143776522]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 0 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨366536992781479321, 366536992781500014⟩, ⟨(-564635438173345598), (-564635438172045870)⟩, true⟩

def words08 : List Nat := [360403493460287726, 360403493460288202, 360507657865279515, 360615102193920720, 360640943484259501, 360640943484260014, 360578012333479873, 360436847329319862, 360298854572444260, 360332207746642368]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 0 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨344405256661344050, 344405256661370381⟩, ⟨1515092119513520055, 1515092119515357135⟩, true⟩

def words09 : List Nat := [360352089968592224, 360371544615876602, 360371544615877110, 360327469252745607, 360205531323864951, 360035792026113510, 359869552507697019, 359787482332671246, 359709217464555166, 359556177856523953]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 0 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 0 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk000
