import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk206

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362521948242825174, 362521953938947491⟩, ⟨(-764765023076072345), (-764685665882164843)⟩, true⟩

def state01 : KState := ⟨⟨362441371133124008, 362441376835039339⟩, ⟨895326048073102596, 895405524632157020⟩, true⟩

def words00 : List Nat := [371284836435486310, 371284836436126922, 371284834660018939, 371284834091237484, 371284833522203169, 371284833371937325, 371284830088796548, 371284826815095618, 371284823541431062, 371284822032741045]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362446540386233204, 362446546093905866⟩, ⟨788968652167054062, 789048247414876594⟩, true⟩

def words01 : List Nat := [371284820162144121, 371284820399642707, 371284820646182887, 371284820646828088, 371284818798550724, 371284817148086268, 371284815825616875, 371284815826261115, 371284814110429843, 371284812255274192]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362453400143271271, 362453405856689144⟩, ⟨647676436581320136, 647756150324996380⟩, true⟩

def words02 : List Nat := [371284810400021869, 371284810017465675, 371284809360745074, 371284809921156734, 371284809921656961, 371284809772589515, 371284806497440744, 371284805562929320, 371284804628184787, 371284804603675329]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486038111080138, 362486043830349494⟩, ⟨(-25805775346717482), (-25725940857424482)⟩, true⟩

def words03 : List Nat := [371284803082237259, 371284801372069928, 371284799922478323, 371284799923186223, 371284799423367839, 371284799536657853, 371284799633288274, 371284799633931735, 371284797417683338, 371284797478871493]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459245374102562, 362459251099094470⟩, ⟨527379192950245957, 527459145582560315⟩, true⟩

def words04 : List Nat := [371284799876707062, 371284799877348895, 371284799153777810, 371284797933496813, 371284796713091726, 371284796218404760, 371284794736971549, 371284794459511801, 371284794181856835, 371284793914861180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362509659592833637, 362509665323618071⟩, ⟨(-513875664085190856), (-513795591807060902)⟩, true⟩

def words05 : List Nat := [371284793532864864, 371284794387990256, 371284796967784363, 371284797052088612, 371284797052591954, 371284796526300672, 371284795999801590, 371284795913914218, 371284796223590405, 371284797427978603]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454373679963218, 362454379416541477⟩, ⟨628496687991908732, 628576879999836258⟩, true⟩

def words06 : List Nat := [371284798350741078, 371284798351383550, 371284796298297658, 371284796438063842, 371284797302476935, 371284797303119469, 371284795053957668, 371284792808062883, 371284790562133801, 371284789522008330]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362402691609818282, 362402697352196987⟩, ⟨1697125747019729906, 1697206058951932858⟩, true⟩

def words07 : List Nat := [371284788051304145, 371284787566500419, 371284787081519554, 371284786584074111, 371284782975645101, 371284780051568690, 371284777127451923, 371284775121023849, 371284771245703047, 371284767277678222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362412691104158876, 362412696852287530⟩, ⟨1490460613148676556, 1490541044019775500⟩, true⟩

def words08 : List Nat := [371284763309741757, 371284761669478276, 371284758876436231, 371284757007141113, 371284755137841563, 371284752809449124, 371284747373395057, 371284743916575865, 371284740459751962, 371284738468721546]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362406671972026340, 362406677726020195⟩, ⟨1615146743178258942, 1615227295429708656⟩, true⟩

def words09 : List Nat := [371284734987426287, 371284731049483897, 371284727111655447, 371284725498633477, 371284722717701369, 371284720659987736, 371284718602247685, 371284716554923712, 371284711799111652, 371284708030147235]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk206
