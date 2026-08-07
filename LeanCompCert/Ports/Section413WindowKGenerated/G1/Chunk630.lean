import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk630

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501437702232958, 362501496121183555⟩, ⟨(-1015776897122915737), (-1013290989127113321)⟩, true⟩

def state01 : KState := ⟨⟨362494792947743714, 362494851385734519⟩, ⟨(-597065554436512871), (-594578446807436917)⟩, true⟩

def words00 : List Nat := [371285412888721312, 371285413145270497, 371285413400402507, 371285413656234238, 371285413987825787, 371285414194809148, 371285414505119767, 371285414816311555, 371285415128213823, 371285415280184577]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502541378732105, 362502599836038485⟩, ⟨(-1085296650221375396), (-1082808325419313328)⟩, true⟩

def words01 : List Nat := [371285415542504154, 371285415805893823, 371285416282511143, 371285416553336179, 371285416784602865, 371285417016547414, 371285417360480752, 371285417580397380, 371285417854510786, 371285418129537171]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483776646999666, 362483835123648311⟩, ⟨97263706420207859, 99753250269397673⟩, true⟩

def words02 : List Nat := [371285418355649663, 371285418357790111, 371285418287201689, 371285418328801370, 371285418444773444, 371285418446913969, 371285418227510317, 371285417986309641, 371285417752481260, 371285417754939274]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470998253412970, 362471056749334939⟩, ⟨902825784256892006, 905316543001445292⟩, true⟩

def words03 : List Nat := [371285417957954463, 371285418186961041, 371285418414298160, 371285418416439098, 371285418308293835, 371285418214160760, 371285418183655505, 371285418185797379, 371285417960480483, 371285417735105902]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480055753067532, 362480114268178707⟩, ⟨331835579450208467, 334327547978169373⟩, true⟩

def words04 : List Nat := [371285417508764397, 371285417408825389, 371285417260320851, 371285417278121728, 371285417279795962, 371285417263335547, 371285416974230978, 371285416897378669, 371285416844029173, 371285416846259249]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486032350583359, 362486090885178166⟩, ⟨(-45014712803431984), (-42521515732462442)⟩, true⟩

def words05 : List Nat := [371285416763760429, 371285416681106714, 371285416671891023, 371285416674274881, 371285416701450934, 371285416754847299, 371285416806596909, 371285416808739543, 371285416580048508, 371285416593369720]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481050496799529, 362481109050489660⟩, ⟨269137642656950519, 271632043977757191⟩, true⟩

def words06 : List Nat := [371285416787818176, 371285416789960064, 371285416649535789, 371285416438107447, 371285416225846708, 371285416090810053, 371285415860161276, 371285415872140655, 371285415882601033, 371285415884863812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510691601748742, 362510750174828854⟩, ⟨(-1600456257003743328), (-1597960632662889554)⟩, true⟩

def words07 : List Nat := [371285415956260486, 371285416097106177, 371285416488172789, 371285416706305664, 371285416879459482, 371285417053262950, 371285417330227406, 371285417482843399, 371285417885893142, 371285418289908468]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482534784511384, 362482593376940080⟩, ⟨175795650758788191, 178292495708456975⟩, true⟩

def words08 : List Nat := [371285418673530443, 371285418722805938, 371285419011750315, 371285419301816692, 371285419582201477, 371285419584344502, 371285419530001770, 371285419445808703, 371285419376940990, 371285419379408118]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473715757144262, 362473774368857387⟩, ⟨732250650418692079, 734748712122647125⟩, true⟩

def words09 : List Nat := [371285419395317149, 371285419456843726, 371285419516860950, 371285419519004164, 371285419244199364, 371285419046858214, 371285418899621187, 371285418901801823, 371285418746126574, 371285418563978190]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk630
