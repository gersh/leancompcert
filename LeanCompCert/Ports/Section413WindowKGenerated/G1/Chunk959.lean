import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494715884417737, 362494855733902724⟩, ⟨(-929532252444872478), (-920477300473486876)⟩, true⟩

def state01 : KState := ⟨⟨362480041435108563, 362480181314918278⟩, ⟨477798371482439905, 486856231746080803⟩, true⟩

def words00 : List Nat := [371285257633083567, 371285257636446154, 371285257628775998, 371285257667930013, 371285257737959248, 371285257741322299, 371285257680477806, 371285257599868747, 371285257517937644, 371285257492915840]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487032326884135, 362487172237007091⟩, ⟨(-192679878136336033), (-183619110376121213)⟩, true⟩

def words01 : List Nat := [371285257498199885, 371285257557816651, 371285257616769189, 371285257634463912, 371285257683698591, 371285257734560648, 371285257892555489, 371285257916373655, 371285257938844412, 371285257962652403]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490679104051239, 362490819044289024⟩, ⟨(-542488532113264331), (-533424875584139447)⟩, true⟩

def words02 : List Nat := [371285258022335349, 371285258034093901, 371285258153223513, 371285258273690379, 371285258374754256, 371285258378117901, 371285258343250440, 371285258356691017, 371285258477107270, 371285258538554860]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484734447164331, 362484874418040552⟩, ⟨27802972593196200, 36869568417560862⟩, true⟩

def words03 : List Nat := [371285258566402620, 371285258595303859, 371285258674651600, 371285258705594360, 371285258741414717, 371285258778531206, 371285258818173642, 371285258821537846, 371285258716045887, 371285258716231271]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488176356321225, 362488316357183464⟩, ⟨(-302400659251935205), (-293331186415616557)⟩, true⟩

def words04 : List Nat := [371285258794541228, 371285258820733064, 371285258845496032, 371285258871426535, 371285258924633675, 371285258928341439, 371285259033039425, 371285259142268008, 371285259228243800, 371285259263600119]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499839151152090, 362499979182453236⟩, ⟨(-1421526848952575426), (-1412454455348012954)⟩, true⟩

def words05 : List Nat := [371285259393510052, 371285259525208968, 371285259678358898, 371285259687712694, 371285259690315591, 371285259683771960, 371285259774346140, 371285259822726898, 371285259978398482, 371285260135597243]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486433024608182, 362486573086309086⟩, ⟨(-135056307142014686), (-125980996217864776)⟩, true⟩

def words06 : List Nat := [371285260285760795, 371285260291939303, 371285260341944139, 371285260393644772, 371285260455150853, 371285260458531912, 371285260416509908, 371285260376142194, 371285260370136282, 371285260387720785]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476321512973701, 362476461604910537⟩, ⟨835454054036516333, 844532266857717795⟩, true⟩

def words07 : List Nat := [371285260512412320, 371285260638441669, 371285260762849572, 371285260766215998, 371285260765853107, 371285260768612656, 371285260813114821, 371285260816482059, 371285260737084761, 371285260649157857]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493844094356018, 362493984216411708⟩, ⟨(-846444480528697640), (-837363376745825914)⟩, true⟩

def words08 : List Nat := [371285260559765697, 371285260554201584, 371285260541371473, 371285260584229498, 371285260611629901, 371285260615018655, 371285260581347275, 371285260621717311, 371285260769057264, 371285260863422930]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494036016442270, 362494176169247155⟩, ⟨(-864863241755760969), (-855779186208849649)⟩, true⟩

def words09 : List Nat := [371285260936403863, 371285261010524823, 371285261173124331, 371285261282780500, 371285261419567996, 371285261557612714, 371285261675093671, 371285261703348323, 371285261798495723, 371285261895581164]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959
