import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk290A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk290B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk290A

def state06 : KState := ⟨⟨360654758018622933, 360654763083852467⟩, ⟨(-2084454655739911891), (-2084355104958136185)⟩, true⟩

def words05 : List Nat := [360583025454473692, 360583027539419486, 360583030021879261, 360583031673719384, 360583032279730079, 360583032885727498, 360583033411886981, 360583034699340100, 360583037167936734, 360583039636450171]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360657901240042294, 360657906308935051⟩, ⟨(-2175998129699954713), (-2175898472447171667)⟩, true⟩

def words06 : List Nat := [360583041502727369, 360583043194282803, 360583046066746935, 360583048939132885, 360583051510815535, 360583052906896454, 360583053711252070, 360583054515596208, 360583055999841447, 360583058575026787]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360616175652241563, 360616180724756435⟩, ⟨(-962950494928828910), (-962850732362920812)⟩, true⟩

def words07 : List Nat := [360583061120237608, 360583063665341989, 360583065307841732, 360583065775264815, 360583065929541189, 360583066083908055, 360583067417973909, 360583069175047326, 360583070314029823, 360583071452985763]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360623743304202084, 360623748380346134⟩, ⟨(-1182949827811585780), (-1182849959691213032)⟩, true⟩

def words08 : List Nat := [360583072929100276, 360583075202535270, 360583078333380798, 360583081464087011, 360583083490459003, 360583084342265475, 360583084940441569, 360583085538691648, 360583086641904425, 360583088040045312]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566595939503666, 360566601019314644⟩, ⟨479900761200554336, 480000736009994868⟩, true⟩

def words09 : List Nat := [360583088847792417, 360583089655532539, 360583091244584179, 360583093599070393, 360583094978729899, 360583096358354662, 360583096994023619, 360583096994408386, 360583096456382564, 360583095889967909]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk290B
