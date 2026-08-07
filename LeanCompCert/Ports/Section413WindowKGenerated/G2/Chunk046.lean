import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk046

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360357127623203684, 360357127729350407⟩, ⟨1025613901664091428, 1025614233229140776⟩, true⟩

def state01 : KState := ⟨⟨360828755403134818, 360828755509767754⟩, ⟨(-1145436355043944358), (-1145436021239819726)⟩, true⟩

def words00 : List Nat := [360580038886364397, 360580023889335822, 360580079685337808, 360580135457116723, 360580150742198824, 360580174166849776, 360580210449904361, 360580246717229722, 360580287826148344, 360580341712057969]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360414026121060294, 360414026228185993⟩, ⟨768545112463687517, 768545448541862843⟩, true⟩

def words01 : List Nat := [360580364646478557, 360580387570961314, 360580408659907303, 360580453613152909, 360580469364354758, 360580485108741649, 360580485108788312, 360580472586238981, 360580414071499374, 360580378056874708]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360219243189728232, 360219243297341405⟩, ⟨1669379773368835370, 1669380111701631066⟩, true⟩

def words02 : List Nat := [360580352360240384, 360580352360292130, 360580316699769897, 360580247991157140, 360580179312247833, 360580089559552660, 360580024471005665, 360579957710464636, 360579890978762308, 360579800556888194]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360712715157148120, 360712715265250866⟩, ⟨(-619146323844959822), (-619145983242950976)⟩, true⟩

def words03 : List Nat := [360579722699608269, 360579649913314460, 360579577158426633, 360579527382194617, 360579481330715291, 360579394546548148, 360579307799802331, 360579267021554287, 360579278630877576, 360579307382630106]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360874638494944191, 360874638603543648⟩, ⟨(-1373127148571689959), (-1373126805662504251)⟩, true⟩

def words04 : List Nat := [360579307382677576, 360579295138291587, 360579308448730645, 360579338015221826, 360579355065225582, 360579358042421866, 360579358042468360, 360579337621257800, 360579342516245139, 360579406007185338]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360760614135545670, 360760614244636169⟩, ⟨(-841727074494150483), (-841726729299133003)⟩, true⟩

def words05 : List Nat := [360579515162508730, 360579624270923672, 360579696671285541, 360579758853643128, 360579785850366740, 360579812835509086, 360579885402912574, 360579947421333475, 360579986191084598, 360580024944207263]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360861451902695722, 360861452012280283⟩, ⟨(-1310437113460463379), (-1310436765960664947)⟩, true⟩

def words06 : List Nat := [360580086754607264, 360580187863778067, 360580334391984970, 360580480857381795, 360580587781357905, 360580649768040869, 360580723062999050, 360580796326575641, 360580844567695031, 360580904642132421]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360819838301412817, 360819838411496684⟩, ⟨(-1115769112275328618), (-1115768762441276930)⟩, true⟩

def words07 : List Nat := [360580940757380673, 360580976857177116, 360581058239164714, 360581171910839541, 360581245507533482, 360581319072764556, 360581369559313920, 360581375329016988, 360581426282709625, 360581477214649584]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360821317718211837, 360821317828790701⟩, ⟨(-1124020941520602808), (-1124020589367479022)⟩, true⟩

def words08 : List Nat := [360581550552519635, 360581579201171026, 360581579201218628, 360581570619929950, 360581562042296161, 360581557302923278, 360581597589610364, 360581637859123849, 360581654590064398, 360581705680129973]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360717627223111775, 360717627334187518⟩, ⟨(-637110806421116577), (-637110451935211289)⟩, true⟩

def words09 : List Nat := [360581801682504628, 360581897643981620, 360581989577563239, 360582036949328944, 360582045529956466, 360582054106934471, 360582054106978193, 360582043071069300, 360582071918827639, 360582100754324678]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk046
