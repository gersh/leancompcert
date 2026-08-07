import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk321

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501285688504240, 362501300047531430⟩, ⟨(-523851902504385638), (-523540360134238832)⟩, true⟩

def state01 : KState := ⟨⟨362496002392952771, 362496016761200930⟩, ⟨(-354154562750375636), (-353842724338976674)⟩, true⟩

def words00 : List Nat := [371284992225418414, 371284992758873248, 371284993142207944, 371284993525867465, 371284994209451648, 371284994407915978, 371284995391351317, 371284996375137596, 371284997055222947, 371284997399476320]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362545031016347812, 362545045393958357⟩, ⟨(-1928743452521716613), (-1928431313437881583)⟩, true⟩

def words01 : List Nat := [371284998610317248, 371284999821642650, 371285001648431916, 371285002185664116, 371285002562890679, 371285002940426787, 371285004283248817, 371285005188040439, 371285007057989701, 371285008928299197]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491484976755828, 362491499363721926⟩, ⟨(-208700726030030401), (-208388286399253065)⟩, true⟩

def words02 : List Nat := [371285010773500135, 371285011329602671, 371285012099843989, 371285012870545534, 371285013915176177, 371285013916211266, 371285013671874424, 371285013431117840, 371285013577059861, 371285013780129780]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362439735848833157, 362439750245096468⟩, ⟨1454348750121746186, 1454661488520788510⟩, true⟩

def words03 : List Nat := [371285014246444782, 371285014713137011, 371285015182801435, 371285015183836702, 371285014365143447, 371285013847094883, 371285013328540763, 371285013213604957, 371285011810530130, 371285010403420077]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362458709348539424, 362458723754077350⟩, ⟨844629431218044730, 844942467749421320⟩, true⟩

def words04 : List Nat := [371285008995947724, 371285008553145912, 371285007967140665, 371285008156981329, 371285008187285014, 371285008188320641, 371285006931169852, 371285006077380933, 371285005223110124, 371285005012794284]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362458759978181360, 362458774393171052⟩, ⟨842936455801698226, 843249796255190634⟩, true⟩

def words05 : List Nat := [371285004196150172, 371285003183579103, 371285002170646638, 371285001455499858, 371285000327760437, 371284999371295954, 371284998414559242, 371284997439115393, 371284995661075227, 371284994847034709]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362439434142833228, 362439448567047614⟩, ⟨1464620929463587348, 1464934566631527088⟩, true⟩

def words06 : List Nat := [371284994032451432, 371284993950624616, 371284992944440418, 371284991874500709, 371284990804242484, 371284989770138346, 371284988255088361, 371284987454230338, 371284986653063808, 371284985855410422]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470117398837701, 362470131832421195⟩, ⟨477455298472973965, 477769237093012467⟩, true⟩

def words07 : List Nat := [371284984440637918, 371284983839501127, 371284983598001318, 371284983599037954, 371284982674777724, 371284981534485586, 371284980393831074, 371284979930592358, 371284979068194424, 371284978607967902]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470856747394413, 362470871190335197⟩, ⟨453499522011767425, 453813761796601057⟩, true⟩

def words08 : List Nat := [371284978147393145, 371284977559781276, 371284975687353914, 371284974777342588, 371284973866855062, 371284973077533219, 371284971855930090, 371284970638071651, 371284969419871936, 371284969163674638]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362445745837813349, 362445760290113644⟩, ⟨1262078846263817819, 1262393387378649247⟩, true⟩

def words09 : List Nat := [371284969249921598, 371284969774519520, 371284970130926399, 371284970131963803, 371284969204596918, 371284968465834120, 371284967726597061, 371284967490276465, 371284966270076388, 371284965053696832]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk321
