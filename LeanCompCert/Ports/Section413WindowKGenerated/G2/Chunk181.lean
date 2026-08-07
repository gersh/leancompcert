import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk181

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360490653057156911, 360490654941643787⟩, ⟨1691529884954917746, 1691552972763200932⟩, true⟩

def state01 : KState := ⟨⟨360544631458556777, 360544633345219811⟩, ⟨714524252844928346, 714547380052394802⟩, true⟩

def words00 : List Nat := [360584105744148562, 360584101935957470, 360584100900864975, 360584101287626290, 360584101287838946, 360584098685856239, 360584095699362232, 360584093982431796, 360584092265625790, 360584089302152578]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360519220717264564, 360519222606118087⟩, ⟨1174860105476265160, 1174883272364624906⟩, true⟩

def words01 : List Nat := [360584087123794603, 360584083412384594, 360584079701340540, 360584077874077729, 360584077574078528, 360584076498437511, 360584075422889598, 360584071832098645, 360584065217057622, 360584061638809292]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360635766845640766, 360635768736669011⟩, ⟨(-937596501839614836), (-937573295534822996)⟩, true⟩

def words02 : List Nat := [360584058060880204, 360584058136241014, 360584058136449732, 360584056411886148, 360584054687475429, 360584051633364615, 360584052475196370, 360584054413197459, 360584054820511571, 360584057672991618]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360646558374596276, 360646560267798459⟩, ⟨(-1133007579437703152), (-1132984333708355542)⟩, true⟩

def words03 : List Nat := [360584063558045891, 360584069442518129, 360584078358885699, 360584084253800500, 360584087622871572, 360584090991586239, 360584094251794341, 360584099032810151, 360584102476285999, 360584105919432418]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360655021447887714, 360655023343287040⟩, ⟨(-1287059059763616142), (-1287035774167447386)⟩, true⟩

def words04 : List Nat := [360584107833685252, 360584107914187733, 360584111023984586, 360584114133512633, 360584115713901133, 360584115714131955, 360584115580068657, 360584113470873112, 360584112281084780, 360584116188079755]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360594367698800165, 360594369596372933⟩, ⟨(-185947583602079882), (-185924258546717736)⟩, true⟩

def words05 : List Nat := [360584119987925563, 360584123787393589, 360584126048233447, 360584126827391397, 360584126832548564, 360584126837766569, 360584128821707477, 360584130912160216, 360584131476170063, 360584132040150990]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360668010500900445, 360668012400652814⟩, ⟨(-1524018910007290891), (-1523995545359446501)⟩, true⟩

def words06 : List Nat := [360584132040340011, 360584132433950142, 360584135112633112, 360584137791065584, 360584137791282054, 360584137614093875, 360584135727691832, 360584135520873531, 360584138127141003, 360584142743211868]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606529876556610, 360606531778514894⟩, ⟨(-406449192965802715), (-406425788225833387)⟩, true⟩

def words07 : List Nat := [360584145846938224, 360584148950351697, 360584153041238604, 360584159104070320, 360584164342422624, 360584169580235997, 360584173122644554, 360584174894389551, 360584176124331554, 360584177354213380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602576704818114, 360602578608954432⟩, ⟨(-334703853613092339), (-334680409265402195)⟩, true⟩

def words08 : List Nat := [360584181600315565, 360584182844070458, 360584182844278429, 360584181486934302, 360584180129701862, 360584178235542607, 360584179289207809, 360584180342800418, 360584180343008548, 360584180477501219]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360698593433151536, 360698595339475705⟩, ⟨(-2081922809097576247), (-2081899324941957651)⟩, true⟩

def words09 : List Nat := [360584184501675342, 360584188525474437, 360584191487483579, 360584194060073554, 360584194060286873, 360584194043573502, 360584195705100740, 360584198980730132, 360584205266431760, 360584211551500212]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk181
