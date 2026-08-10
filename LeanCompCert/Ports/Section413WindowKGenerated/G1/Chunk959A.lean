import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk959A
