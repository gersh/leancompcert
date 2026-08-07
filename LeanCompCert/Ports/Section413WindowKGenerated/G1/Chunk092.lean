import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk092

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362525011887730942, 362525012944841185⟩, ⟨(-398108191152927996), (-398101606024152582)⟩, true⟩

def state01 : KState := ⟨⟨362437958961686978, 362437960021205607⟩, ⟨402946855455193036, 402953462753712444⟩, true⟩

def words00 : List Nat := [371281750435317653, 371281750435585012, 371281745463364097, 371281748859615753, 371281752632917189, 371281752633184634, 371281740732504277, 371281727153114251, 371281713576563410, 371281711754403622]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362376858882701612, 362376859944633783⟩, ⟨966426135128167463, 966432764667654551⟩, true⟩

def words01 : List Nat := [371281711524062942, 371281716042795471, 371281719518769896, 371281719519038297, 371281711303234761, 371281704843272475, 371281699597768287, 371281699598037872, 371281690486115790, 371281679116506631]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362523321445654455, 362523322509984906⟩, ⟨(-384349023339778315), (-384342371675688551)⟩, true⟩

def words02 : List Nat := [371281668110328684, 371281668110623965, 371281668243871839, 371281672350556907, 371281673802682494, 371281673802955204, 371281669067232676, 371281672555331850, 371281681949394523, 371281686460621274]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362535328945115533, 362535330011898698⟩, ⟨(-495317948296949060), (-495311273982261810)⟩, true⟩

def words03 : List Nat := [371281689611961187, 371281692762711095, 371281700721778732, 371281704142548170, 371281711088787706, 371281718033622732, 371281724968954276, 371281724969223071, 371281724895325332, 371281730696458566]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467542725993570, 362467543795168401⟩, ⟨131622083217952286, 131628779644095706⟩, true⟩

def words04 : List Nat := [371281748170562019, 371281750086880256, 371281751976556170, 371281753865908052, 371281758590896303, 371281758816162775, 371281763853702329, 371281768890262200, 371281773933229777, 371281773933508304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362618733441351743, 362618734512954131⟩, ⟨(-1267852262508996294), (-1267845543615340686)⟩, true⟩

def words05 : List Nat := [371281774707997967, 371281777020351258, 371281787803381791, 371281788942291366, 371281788942499792, 371281788184044361, 371281798297486382, 371281803359688930, 371281818147253750, 371281832931740943]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489699798677739, 362489700872716446⟩, ⟨(-72465993395357318), (-72459251929005382)⟩, true⟩

def words06 : List Nat := [371281845429848832, 371281847679591890, 371281858823246534, 371281869964637078, 371281882143460791, 371281882143730271, 371281881639728741, 371281881138375865, 371281884340375815, 371281885183801658]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362382937889624193, 362382938966090027⟩, ⟨918141679451966027, 918148443430192313⟩, true⟩

def words07 : List Nat := [371281895731150730, 371281906276336492, 371281914605826476, 371281914606096069, 371281907490681806, 371281900692927458, 371281898683384743, 371281898683654425, 371281888038251660, 371281877375942419]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469044510963933, 362469045589851154⟩, ⟨119355970724322746, 119362757185262254⟩, true⟩

def words08 : List Nat := [371281867630664922, 371281867630969056, 371281875613183107, 371281885388253035, 371281893348645514, 371281893348915617, 371281887047357264, 371281888196478832, 371281894110259072, 371281894110538481]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362436946442826458, 362436947524173690⟩, ⟨418009039890322623, 418015849217253539⟩, true⟩

def words09 : List Nat := [371281892727841730, 371281890572757410, 371281897810983205, 371281901452738693, 371281904997642590, 371281908541892851, 371281912104970735, 371281912105241145, 371281900298250080, 371281895464949739]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk092
