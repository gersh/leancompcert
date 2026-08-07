import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583569322316901, 360583622934365086⟩, ⟨(-150304951415405698), (-147035808044776816)⟩, true⟩

def state01 : KState := ⟨⟨360578105633338636, 360578159257652494⟩, ⟨343076078173695417, 346346329196100791⟩, true⟩

def words00 : List Nat := [360581994760041301, 360581994777166980, 360581994778329008, 360581994726266469, 360581994673988694, 360581994591285427, 360581994585250748, 360581994524196079, 360581994463000505, 360581994340469415]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604185498616994, 360604239135218408⟩, ⟨(-2012359461674427729), (-2009088100901475503)⟩, true⟩

def words01 : List Nat := [360581994299062675, 360581994294654486, 360581994406522280, 360581994527535824, 360581994538105707, 360581994548764376, 360581994631179424, 360581994775582649, 360581995022920096, 360581995270547939]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591965916861486, 360592019565901303⟩, ⟨(-908753196005602593), (-905480711735490269)⟩, true⟩

def words02 : List Nat := [360581995392399281, 360581995393703010, 360581995463666060, 360581995535811409, 360581995576095150, 360581995577401719, 360581995564462458, 360581995490186903, 360581995422802632, 360581995535261374]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575564345515752, 360575618006826579⟩, ⟨572926984650581659, 576200577423904605⟩, true⟩

def words03 : List Nat := [360581995741371941, 360581995947736750, 360581996092842536, 360581996192633111, 360581996193744316, 360581996189620484, 360581996216203270, 360581996217510801, 360581996209546021, 360581996140293747]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587625868589971, 360587679542231979⟩, ⟨(-516759138516506488), (-513484431685490028)⟩, true⟩

def words04 : List Nat := [360581996086265087, 360581996200644437, 360581996294970012, 360581996389537823, 360581996390743205, 360581996383980540, 360581996279909026, 360581996274817782, 360581996269361903, 360581996324207990]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590650768602261, 360590704454668017⟩, ⟨(-790065506977471500), (-786789677599199742)⟩, true⟩

def words05 : List Nat := [360581996327205268, 360581996330333821, 360581996455583883, 360581996686533792, 360581996845414864, 360581997004525427, 360581997102024550, 360581997103328847, 360581997174750776, 360581997272613822]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583713888287901, 360583767586656310⟩, ⟨(-163262475910962820), (-159985534802945416)⟩, true⟩

def words06 : List Nat := [360581997469889021, 360581997545084785, 360581997546272840, 360581997519782737, 360581997493084471, 360581997372683294, 360581997313442890, 360581997312308907, 360581997311044740, 360581997267252929]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604581231684874, 360604634942362946⟩, ⟨(-2049151883641782195), (-2045873830047533815)⟩, true⟩

def words07 : List Nat := [360581997410216142, 360581997553563397, 360581997818837062, 360581997994671505, 360581998065460838, 360581998136363756, 360581998204162918, 360581998333776612, 360581998585291535, 360581998837096933]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578135309812920, 360578189032915934⟩, ⟨341083361980158980, 344362538600940788⟩, true⟩

def words08 : List Nat := [360581999018362159, 360581999077494424, 360581999143547104, 360581999210004116, 360581999245393647, 360581999246698913, 360581999204542764, 360581999068841135, 360581998932900161, 360581998774464789]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563814648998507, 360563868384402325⟩, ⟨1635542123048762450, 1638822411600590364⟩, true⟩

def words09 : List Nat := [360581998733391208, 360581998654219317, 360581998574907929, 360581998421189591, 360581998145026526, 360581997818785489, 360581997492152236, 360581997288074058, 360581997150089115, 360581996950902332]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903
