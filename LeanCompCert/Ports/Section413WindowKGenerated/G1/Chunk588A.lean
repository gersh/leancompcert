import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk588A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492518080133720, 362492568692344048⟩, ⟨(-444399170133406669), (-442388896238500121)⟩, true⟩

def state01 : KState := ⟨⟨362476237444266482, 362476288074154403⟩, ⟨513020488345313346, 515031801775450872⟩, true⟩

def words00 : List Nat := [371285045589254333, 371285045593909134, 371285045595398535, 371285045567694387, 371285045578090036, 371285045580317308, 371285045553556791, 371285045591059033, 371285045626965209, 371285045629022206]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501843715906745, 362501894363736567⟩, ⟨(-993003531016668079), (-990991162331843439)⟩, true⟩

def words01 : List Nat := [371285045539134088, 371285045599173358, 371285045907036386, 371285045976198308, 371285045997441435, 371285046019316437, 371285046187791661, 371285046213101687, 371285046500885742, 371285046789531235]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483884222388517, 362483934888177245⟩, ⟨63389023915010910, 65402449031916238⟩, true⟩

def words02 : List Nat := [371285047024276623, 371285047026264393, 371285046956700982, 371285047040326896, 371285047175528216, 371285047177516371, 371285046970944429, 371285046764208251, 371285046605252620, 371285046607521660]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476055255447167, 362476105939138877⟩, ⟨524083627239661102, 526098105683091712⟩, true⟩

def words03 : List Nat := [371285046860238335, 371285047132677159, 371285047402899899, 371285047404891120, 371285047364131610, 371285047299896248, 371285047347987765, 371285047349987564, 371285047253117914, 371285047103409494]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485019853823562, 362485070555340547⟩, ⟨(-3389994596488293), (-1374467223917577)⟩, true⟩

def words04 : List Nat := [371285047014904290, 371285047017154321, 371285047130408321, 371285047284678280, 371285047394737425, 371285047396726220, 371285047121579039, 371285047108321741, 371285047197832726, 371285047200304543]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk588A
