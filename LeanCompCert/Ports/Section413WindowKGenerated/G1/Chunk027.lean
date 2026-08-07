import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk027

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362527448254648302, 362527448335230024⟩, ⟨(-172793142380337695), (-172792994722105863)⟩, true⟩

def state01 : KState := ⟨⟨362491696803251469, 362491696884458058⟩, ⟨(-75175348946473499), (-75175199597851895)⟩, true⟩

def words00 : List Nat := [371263595577273674, 371263606348785350, 371263606348837840, 371263599981105872, 371263626220375209, 371263626220452779, 371263738973899768, 371263863069871427, 371263956958334536, 371263967190766486]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨363065326213190392, 363065326295033702⟩, ⟨(-1631810987150762388), (-1631810836073409090)⟩, true⟩

def words01 : List Nat := [371264112785084405, 371264258272107881, 371264538921983245, 371264684755966579, 371264811282425408, 371264937715769845, 371265089468174520, 371265175196680763, 371265395840514902, 371265616322202608]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362771764161968407, 362771764244449320⟩, ⟨(-833831956331522162), (-833831803516602274)⟩, true⟩

def words02 : List Nat := [371265835160155085, 371265875165259491, 371265968519498238, 371266061805254638, 371266194859112973, 371266200859888922, 371266200859942322, 371266199713467103, 371266331349306152, 371266443188602890]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362282867640808547, 362282867723928198⟩, ⟨505763870584149992, 505764025146137416⟩, true⟩

def words03 : List Nat := [371266688807702164, 371266934247086232, 371267178119434837, 371267244680947332, 371267348177916187, 371267451599293422, 371267564092623429, 371267564092694676, 371267520526020033, 371267453134565475]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362596640859190703, 362596640942948194⟩, ⟨(-354893283654093499), (-354893127341087313)⟩, true⟩

def words04 : List Nat := [371267451407617595, 371267452018636200, 371267535036987352, 371267617994881899, 371267675271203880, 371267675271275296, 371267556871181322, 371267523510418005, 371267588896567911, 371267635807600653]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362773382408943544, 362773382493353977⟩, ⟨(-841723619940470901), (-841723461828613721)⟩, true⟩

def words05 : List Nat := [371267657029453084, 371267678235912304, 371267831236932471, 371267929732995529, 371268049422754215, 371268169025713599, 371268286905525349, 371268299687189165, 371268410224486584, 371268520681753610]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362443079384132334, 362443079469181700⟩, ⟨71388007328957598, 71388167207689310⟩, true⟩

def words06 : List Nat := [371268693355136633, 371268693355208441, 371268692306995626, 371268690059015199, 371268693902291038, 371268693902370040, 371268708923382165, 371268781655349866, 371268851370626270, 371268851370700722]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362792296034457232, 362792296120158390⟩, ⟨(-897468479750947065), (-897468318063446395)⟩, true⟩

def words07 : List Nat := [371268905261482968, 371268968407305519, 371269121009117105, 371269151986497109, 371269152370746393, 371269152754741784, 371269282796888966, 371269349621984420, 371269465789839505, 371269581874180884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362657530121681760, 362657530208036503⟩, ⟨(-523643447496923504), (-523643283989140482)⟩, true⟩

def words08 : List Nat := [371269694569429492, 371269694569502186, 371269729649660524, 371269767947090619, 371269841298917585, 371269841298991211, 371269811503132317, 371269779604413415, 371269844443082709, 371269911689946521]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362587022873426223, 362587022960435944⟩, ⟨(-324877744149750328), (-324877578811213446)⟩, true⟩

def words09 : List Nat := [371270107364017787, 371270302898001349, 371270472491722061, 371270534481481068, 371270617685730614, 371270700830519261, 371270912056801720, 371270953800307608, 371270995253633950, 371271036677390170]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk027
