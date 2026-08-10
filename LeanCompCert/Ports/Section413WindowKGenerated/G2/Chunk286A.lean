import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk286A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589855369129298, 360589860268580156⟩, ⟨(-215994156497538028), (-215899385213747242)⟩, true⟩

def state01 : KState := ⟨⟨360640291011192796, 360640295914208330⟩, ⟨(-1658505464065354962), (-1658410590813651446)⟩, true⟩

def words00 : List Nat := [360582312555519765, 360582314497523410, 360582317657427642, 360582320817183107, 360582322933643893, 360582323835951344, 360582325956079450, 360582328076169759, 360582329797396194, 360582331823795075]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606453774317838, 360606458680934993⟩, ⟨(-690413400414737698), (-690318424103517728)⟩, true⟩

def words01 : List Nat := [360582332752814615, 360582333681804713, 360582334459754869, 360582336007083083, 360582336898101273, 360582337789125336, 360582338070807889, 360582338071185948, 360582338539895457, 360582339383073161]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360659883351709648, 360659888261891633⟩, ⟨(-2219914011100059943), (-2219818932745545413)⟩, true⟩

def words02 : List Nat := [360582341443151327, 360582343328541484, 360582344175631115, 360582345022696663, 360582345489680003, 360582346746493213, 360582349219717000, 360582351692841254, 360582353545016476, 360582356253483071]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360662594958736888, 360662599872485971⟩, ⟨(-2297578748118712324), (-2297483567620341560)⟩, true⟩

def words03 : List Nat := [360582360178024550, 360582364102402438, 360582367663878876, 360582370401260054, 360582372016741906, 360582373632140043, 360582375218087114, 360582377672421937, 360582380473783825, 360582383275034055]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360635814913201897, 360635819830551690⟩, ⟨(-1530786569112834363), (-1530691285472368681)⟩, true⟩

def words04 : List Nat := [360582385468104913, 360582386450176585, 360582388647335620, 360582390844462027, 360582392280941238, 360582392506661668, 360582392507002198, 360582392119874658, 360582392560121114, 360582394425313745]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk286A
