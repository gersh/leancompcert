import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593528899795849, 360593552138009830⟩, ⟨(-678491387129500391), (-677543168101867025)⟩, true⟩

def state01 : KState := ⟨⟨360595165542949668, 360595188789149184⟩, ⟨(-777479028852597180), (-776530327457633306)⟩, true⟩

def words00 : List Nat := [360582334753031933, 360582334921517457, 360582335081658953, 360582335241945361, 360582335242724667, 360582335171461302, 360582334826865449, 360582334629064070, 360582334454084832, 360582334667756431]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594023413227407, 360594046667475100⟩, ⟨(-708474826949946025), (-707525639325147271)⟩, true⟩

def words01 : List Nat := [360582334708526841, 360582334749390544, 360582335064125987, 360582335515836161, 360582335854826648, 360582336193943957, 360582336317362678, 360582336348882470, 360582336543381711, 360582336738157063]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581414240020552, 360581437502229273⟩, ⟨53327578296477536, 54277246966663786⟩, true⟩

def words02 : List Nat := [360582336922801199, 360582336923646856, 360582336835328826, 360582336540082801, 360582336244690431, 360582335880962967, 360582335714510823, 360582335768758596, 360582335769511806, 360582335686028159]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603155934430009, 360603179204633400⟩, ⟨(-1260698200405117255), (-1259748048578053943)⟩, true⟩

def words03 : List Nat := [360582335671860821, 360582335578952868, 360582335603532876, 360582335800352486, 360582335801141673, 360582335733784111, 360582335678281712, 360582335905722017, 360582336251266512, 360582336596989946]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590052681295154, 360590075959549689⟩, ⟨(-468807387684327221), (-467856749207432267)⟩, true⟩

def words04 : List Nat := [360582336804900217, 360582336831473967, 360582337131652733, 360582337432079993, 360582337470268960, 360582337471114999, 360582337236505485, 360582336864368931, 360582336492082512, 360582336521836377]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604A
