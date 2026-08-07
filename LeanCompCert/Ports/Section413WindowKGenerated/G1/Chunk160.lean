import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk160

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475253073286251, 362475256433757922⟩, ⟨146739214050439644, 146775584833277320⟩, true⟩

def state01 : KState := ⟨⟨362510661071989852, 362510664436827790⟩, ⟨(-419656131759872536), (-419619691094550202)⟩, true⟩

def words00 : List Nat := [371284432670298212, 371284434681622279, 371284439239484030, 371284443796967700, 371284446866063724, 371284446866551430, 371284447980657696, 371284450490828615, 371284454586785739, 371284456224280507]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362523283559013068, 362523286928295143⟩, ⟨(-621706070178923488), (-621669558340688098)⟩, true⟩

def words01 : List Nat := [371284457753241312, 371284459282167218, 371284463956273087, 371284467054618489, 371284471305391084, 371284475555840308, 371284479705925632, 371284479706413626, 371284481087596028, 371284483510384858]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362457683762737380, 362457687136367985⟩, ⟨429572995253806875, 429609576778520791⟩, true⟩

def words02 : List Nat := [371284488893543318, 371284489088572052, 371284489088943435, 371284488549781062, 371284488632625550, 371284488633162807, 371284487417533028, 371284487508789011, 371284487509159212, 371284487484264337]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485356053401111, 362485359431448939⟩, ⟨(-14208839142236656), (-14172186787006568)⟩, true⟩

def words03 : List Nat := [371284485812814960, 371284485124806237, 371284487640213401, 371284487640701841, 371284485663525144, 371284483110289057, 371284480557183020, 371284478877757385, 371284475878104346, 371284475933737637]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362441312952832915, 362441316335288573⟩, ⟨692406060930406834, 692442784009768174⟩, true⟩

def words04 : List Nat := [371284475972724548, 371284475973215493, 371284472344714071, 371284471876769089, 371284472089423735, 371284472089912700, 371284468370013580, 371284464660637853, 371284460951521032, 371284459187874852]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362428724661060968, 362428728047919531⟩, ⟨894556387035543569, 894593180804236175⟩, true⟩

def words05 : List Nat := [371284456500351961, 371284455397458301, 371284454294542024, 371284453176668606, 371284447947405974, 371284443312051538, 371284438677013294, 371284437921958736, 371284434702879607, 371284431234769110]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362520645582396919, 362520648973630020⟩, ⟨(-581984575612229521), (-581947711566006493)⟩, true⟩

def words06 : List Nat := [371284428176957784, 371284428177496386, 371284429035690355, 371284431403775535, 371284432401409250, 371284432401899153, 371284430161531636, 371284430980100713, 371284435674332692, 371284437928171368]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507447770774747, 362507451166476924⟩, ⟨(-369612239439320169), (-369575303552806867)⟩, true⟩

def words07 : List Nat := [371284439477886341, 371284441027584558, 371284446452042942, 371284450635271202, 371284455989905984, 371284461344056681, 371284466347722763, 371284466348212610, 371284467627086906, 371284469056934433]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362530189229931519, 362530192629995251⟩, ⟨(-735267167557910786), (-735230161514527904)⟩, true⟩

def words08 : List Nat := [371284473014312164, 371284474630433497, 371284476263561758, 371284477896644139, 371284480668865761, 371284482036050673, 371284487270030525, 371284492503562484, 371284497777933260, 371284500618217579]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362588806581357930, 362588809985857383⟩, ⟨(-1678705067273480572), (-1678667989837079858)⟩, true⟩

def words09 : List Nat := [371284507324326198, 371284514029854405, 371284520843756921, 371284524007365641, 371284526154904669, 371284528302335368, 371284534313257848, 371284538415935368, 371284544892764511, 371284551369011406]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk160
