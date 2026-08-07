import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk519

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493411606626057, 362493450645286653⟩, ⟨(-438416007267526989), (-437047222228006077)⟩, true⟩

def state01 : KState := ⟨⟨362475687436303661, 362475726490431063⟩, ⟨481541396856829592, 482910984703926818⟩, true⟩

def words00 : List Nat := [371285030181605668, 371285030183343131, 371285030011381470, 371285029848785122, 371285029685527428, 371285029537900798, 371285029283959103, 371285029343685388, 371285029344999969, 371285029341224821]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494675128251154, 362494714198132445⟩, ⟨(-504198785290310355), (-502828379582452995)⟩, true⟩

def words01 : List Nat := [371285029163199128, 371285029156993722, 371285029512216401, 371285029513954482, 371285029421641850, 371285029267280322, 371285029296866267, 371285029332377032, 371285029520111624, 371285029708627574]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495102211058765, 362495141296617623⟩, ⟨(-526432118889278580), (-525060899119451078)⟩, true⟩

def words02 : List Nat := [371285029893764583, 371285029895511112, 371285029886686001, 371285030048762468, 371285030290988606, 371285030292757178, 371285030227732464, 371285030148766468, 371285030358758369, 371285030555458789]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472226405701272, 362472265506921710⟩, ⟨661678661981066604, 663050695135955410⟩, true⟩

def words03 : List Nat := [371285030941107980, 371285031327424756, 371285031641879542, 371285031643620672, 371285031560066451, 371285031493368475, 371285031685941432, 371285031687680238, 371285031455299185, 371285031211487285]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489970003811601, 362490009120590626⟩, ⟨(-259928000597810707), (-258555159251559777)⟩, true⟩

def words04 : List Nat := [371285031091482368, 371285031093411185, 371285031409871971, 371285031732733269, 371285031992725758, 371285031994468586, 371285031870768008, 371285031830962090, 371285032118610270, 371285032216214357]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490510188853217, 362490549321484873⟩, ⟨(-287974993056286392), (-286601328084797008)⟩, true⟩

def words05 : List Nat := [371285032313441435, 371285032411278573, 371285032698213027, 371285032850042386, 371285033115396667, 371285033381391266, 371285033614698418, 371285033616438067, 371285033512385574, 371285033620707660]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465810374302584, 362465849522459053⟩, ⟨995537598060170009, 996912069780547211⟩, true⟩

def words06 : List Nat := [371285033811673558, 371285033813413149, 371285033511046038, 371285033209520838, 371285032907348171, 371285032682491734, 371285032272436479, 371285032189486947, 371285032105898383, 371285031975216039]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503976244238769, 362504015408087197⟩, ⟨(-988109182143512200), (-986733894833218770)⟩, true⟩

def words07 : List Nat := [371285031608135004, 371285031611035044, 371285031982961046, 371285032002318385, 371285032003713803, 371285031886368665, 371285032018940442, 371285032086801576, 371285032453187163, 371285032820317951]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501975372691093, 362502014552273719⟩, ⟨(-884096063037668899), (-882719957785371531)⟩, true⟩

def words08 : List Nat := [371285033187005927, 371285033310676625, 371285033745310680, 371285034180875935, 371285034684077549, 371285034945459600, 371285035212932543, 371285035480959218, 371285035901360181, 371285036229914362]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480831740521332, 362480870935793591⟩, ⟨215383843152582573, 216760764187139957⟩, true⟩

def words09 : List Nat := [371285036927289850, 371285037625361312, 371285038319941136, 371285038522096867, 371285038837747572, 371285039154262248, 371285039567687308, 371285039569428432, 371285039490200512, 371285039412027960]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk519
