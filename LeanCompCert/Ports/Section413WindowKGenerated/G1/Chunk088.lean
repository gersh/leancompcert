import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk088

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362346308591133669, 362346309554214340⟩, ⟨1191658812726867869, 1191664551428724983⟩, true⟩

def state01 : KState := ⟨⟨362512715341367248, 362512716306727564⟩, ⟨(-273300215377807285), (-273294456603265053)⟩, true⟩

def words00 : List Nat := [371281710594205442, 371281703827776239, 371281690869950310, 371281690749701578, 371281690629403497, 371281688078060918, 371281680850132212, 371281683649921314, 371281695369278396, 371281698890247793]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472553129845829, 362472554097534461⟩, ⟨80692632897021175, 80698412195496683⟩, true⟩

def words01 : List Nat := [371281699840682907, 371281700790982483, 371281707012899893, 371281708883826071, 371281712042975856, 371281715201509841, 371281718441936478, 371281718442191894, 371281704614528474, 371281703577375221]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362390551958035537, 362390552927997638⟩, ⟨804855335254151933, 804861134616720451⟩, true⟩

def words02 : List Nat := [371281714287651569, 371281714766536416, 371281714766728270, 371281713487560021, 371281714490440152, 371281714490721375, 371281710346013086, 371281708104215782, 371281705862845049, 371281703679369861]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362630747389514906, 362630748361792963⟩, ⟨(-1317317344903569741), (-1317311525079667319)⟩, true⟩

def words03 : List Nat := [371281695806054589, 371281698253999368, 371281706710342478, 371281706710602614, 371281704655142606, 371281702269111562, 371281710251415540, 371281714361431849, 371281731220655880, 371281748076182776]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487262794488388, 362487263769078922⟩, ⟨(-48726810136889613), (-48720969858936391)⟩, true⟩

def words04 : List Nat := [371281762268685171, 371281762268941203, 371281766076200527, 371281772680545935, 371281780997627376, 371281780997883607, 371281772341249323, 371281763509831203, 371281758574452699, 371281759196730156]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362377159857548597, 362377160834444199⟩, ⟨926701106056353645, 926706966745925423⟩, true⟩

def words05 : List Nat := [371281769990665326, 371281780782262935, 371281790773368890, 371281790773625798, 371281787812371045, 371281782248205315, 371281778969903300, 371281778970159976, 371281767106508753, 371281755300216877]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362576203311743439, 362576204290940589⟩, ⟨(-837251438196322075), (-837245557103070705)⟩, true⟩

def words06 : List Nat := [371281744381692248, 371281744381979464, 371281749868654088, 371281758951720981, 371281766545983200, 371281767543004186, 371281781211926611, 371281794877895460, 371281813585251678, 371281824225885571]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362585166622801350, 362585167604343986⟩, ⟨(-916572344537624031), (-916566442628103637)⟩, true⟩

def words07 : List Nat := [371281834930962325, 371281845633714291, 371281865642297655, 371281881398408129, 371281900420565639, 371281919438537165, 371281935872329349, 371281939037271212, 371281950662285750, 371281962284827254]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362552877627818225, 362552878611654249⟩, ⟨(-629743735605934186), (-629737813319035374)⟩, true⟩

def words08 : List Nat := [371281984641526290, 371281990161620408, 371281993009807134, 371281995857431252, 371282002572285004, 371282002948372561, 371282015934585331, 371282028917983942, 371282041961966211, 371282049929467877]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362586038280229249, 362586039266391937⟩, ⟨(-924453261902042556), (-924447318919340996)⟩, true⟩

def words09 : List Nat := [371282065733040235, 371282081533191941, 371282109919625012, 371282121514482208, 371282130748905428, 371282139981335936, 371282151705466481, 371282157108504007, 371282168780833287, 371282180450649960]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk088
