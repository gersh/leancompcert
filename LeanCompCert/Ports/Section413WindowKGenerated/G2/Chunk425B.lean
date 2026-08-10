import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk425A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk425B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk425A

def state06 : KState := ⟨⟨360606099417923221, 360606110631830787⟩, ⟨(-999589109113251043), (-999266568897853065)⟩, true⟩

def words05 : List Nat := [360582628977732209, 360582629740003667, 360582630486920307, 360582630684606059, 360582630685140562, 360582630417436274, 360582630433373960, 360582631071337682, 360582631623491249, 360582632175758377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600869936131670, 360600881155564303⟩, ⟨(-777190078693778571), (-776867303304600543)⟩, true⟩

def words06 : List Nat := [360582632450386203, 360582632561366488, 360582632998084917, 360582633434952312, 360582633729053981, 360582633729633887, 360582633474731449, 360582632793347265, 360582632111882594, 360582632411036230]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589214634343014, 360589225859232452⟩, ⟨(-280843725973276796), (-280520718260031470)⟩, true⟩

def words07 : List Nat := [360582633391842572, 360582634372714332, 360582635001844223, 360582635645505349, 360582635952784913, 360582636260200645, 360582637119002455, 360582637616998114, 360582637772247459, 360582637927566685]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608295006197591, 360608306236570751⟩, ⟨(-1093491957044470628), (-1093168715808031780)⟩, true⟩

def words08 : List Nat := [360582637928047210, 360582637934495628, 360582638495609680, 360582639056808390, 360582639076339312, 360582639076919542, 360582638677972627, 360582638592964584, 360582638973330950, 360582639576576667]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609211362401615, 360609222598295347⟩, ⟨(-1132540227398363752), (-1132216751013421294)⟩, true⟩

def words09 : List Nat := [360582639902427263, 360582640228329812, 360582640965317521, 360582642030934083, 360582642717505436, 360582643404131658, 360582643814011843, 360582644115250420, 360582644739627944, 360582645364169073]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk425B
