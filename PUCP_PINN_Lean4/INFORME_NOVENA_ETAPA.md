# Novena etapa: estructura variacional de la pérdida PINN

## Fuente de la tesis

Se revisó la Hipótesis 3.2 (PDF, p. 56–57), las definiciones de pérdida (pp. 44–45 y 61–64), el Lema 3.5 (pp. 64–71), la Hipótesis 3.7 (pp. 77–78) y el Teorema 3.8 (pp. 79–82). Para `d≥2`, la tesis define, con `r_h=L[h]−f` y `b_h=B[h]−g`, pesos residuales fijos `λr,λb>0`, tamaños `mr,mb>0` y medidas probabilísticas `μr,μb`:

- `LossPINN_m(h;λ)=λr/mr ∑ᵢ|r_h(xᵢʳ)|² + λb/mb ∑ⱼ|b_h(xⱼᵇ)|²`.
- `LossPINN(h;λ)=λr∫|r_h|² dμr + λb∫|b_h|² dμb`.
- `Rr(h)=[L[h]]²_{α;U}`, `Rb(h)=[B[h]]²_{α;Γ}` y `J_m(h)=LossPINN_m(h;λ)+λRr,m Rr(h)+λRb,m Rb(h)` (3.22).
- En (3.23), `a_m=max{hatλRr,m,hatλRb,m}` y se fijan ambos pesos de regularización iguales a `a_m`. Los pesos de (3.7) son `hatλRr,m=3λr εr^(2α)/C_m` y `hatλRb,m=3λb εb^(2α)/C_m`, con `C_m=3 max{Cr mr εr²,Cb mb εb}` para el cuadrado (`d=2`).

Estas fórmulas se codifican en `ProblemaPINN`, `perdidaEmpiricaInterior`, `perdidaEmpiricaFrontera`, `perdidaEmpirica`, `perdidaPoblacional`, `regularidadInterior`, `regularidadFrontera`, `funcionalRegularizado`, `factorCoberturaCuadrado`, `pesoCobertura` y `pesoRegularizacionIgual`. `ProblemaPINN` exige que las medidas sean probabilísticas, los tamaños positivos y los pesos residuales positivos. Los valores de seminorma son parámetros del problema; `CotasHolder` expresa la obligación de que controlen realmente los incrementos Hölder. No se ha instanciado todavía una arquitectura neuronal ni una medida concreta de frontera.

## Densidad

La Hipótesis 3.2 exige `ρr≥ρ₀>0` casi en todas partes, continuidad absoluta de `μr` respecto de Lebesgue y la cota de masa `μr(B̄(x,ε)∩U)≤Cr ε²` para radios pequeños. **Estas condiciones son matemáticamente suficientes** para `ρr≤Cr/π` casi en todas partes en `U=(-1,1)²`: `ρr` es localmente integrable por ser densidad de una probabilidad; en casi todo punto interior, las medias de `ρr` sobre bolas convergen a `ρr(x)` por diferenciación de Lebesgue; para radios menores que la distancia a la frontera, la masa está acotada por `Cr ε²` y el volumen de la bola es `π ε²`. La formalización de esta implicación queda **pendiente**: falta conectar la cota de masa con el teorema `IsUnifLocDoublingMeasure.ae_tendsto_average` de Mathlib y la fórmula de volumen de bolas en `ℝ²`. No se ha introducido ese resultado como axioma.

Mientras tanto, `DensidadResidualMinima.lean` define `DensidadInferior` **sin `rhoMax`**. `cota_densidad_sin_superior`, `cota_perdida_sin_superior`, `cota_norma_sin_superior` y `estimacion_error_sin_superior` compilan con una hipótesis visible `ResiduoPonderadoIntegrable D r` para el residuo considerado. La cota inferior por sí sola no garantiza que `ρr²` sea integrable para todo `r∈L²`; la integrabilidad ponderada es exactamente la condición adicional necesaria para interpretar la pérdida como integral real finita. La estructura acotada anterior es un caso particular mediante `acotada_integrable`, sin modificar sus pruebas.

## Minimalidad y comparadores

`EsMinimizadorGlobal H_m h_m` contiene `h_m∈H_m` y la comparación `J_m(h_m)≤J_m(g)` para todo `g∈H_m`. `ComparadorExacto H_m g_m` contiene `g_m∈H_m` y `LossPINN_m(g_m;λ)=0` (3.24). Con pesos iguales positivos `a_m`, los teoremas nuevos conectan los lemas ya verificados de `Minimalidad.lean`:

1. `comparacion_con_interpolador`: `LossPINN_m(h_m;λ)+a_m(Rr(h_m)+Rb(h_m))≤a_m(Rr(g_m)+Rb(g_m))`.
2. `regularidad_minimizador_le_comparador`: `Rr(h_m)+Rb(h_m)≤Rr(g_m)+Rb(g_m)`, paso (3.29).
3. `perdidaEmpirica_minimizador_le`: `LossPINN_m(h_m;λ)≤a_m(Rr(g_m)+Rb(g_m))`.
4. `perdidaEmpirica_le_regularidad_uniforme`: si el comparador satisface `Rr(g_m)+Rb(g_m)≤R*`, entonces `LossPINN_m(h_m;λ)≤a_m R*`.

Estas son implicaciones de minimalidad **probadas**. La existencia de minimizadores y comparadores, su selección mensurable y la uniformidad de `R*` a lo largo de todos los índices son hipótesis, como en 3.7; no se derivan de una arquitectura concreta. La última desigualdad es **empírica**. No se la denomina (3.26), que trata de la pérdida **poblacional**.

## Cobertura y estadística pendiente

`residuo_puntual_de_cobertura` prueba el paso puntual de (3.14): si las muestras cubren el dominio a radio `ε`, `L[h]` y `f` son Hölder con constantes `CL,Cf`, entonces para cada `x` existe una muestra `x_i` tal que

`|L[h](x)−f(x)|² ≤ 3(|L[h](x_i)−f(x_i)|² + CL² ε^(2α) + Cf² ε^(2α))`.

`MuestrasCubren`, `MasaBolaSuperior` y `CotasHolder` formulan las premisas geométricas y analíticas. `ObjetivoCoberturaIntegral` registra la desigualdad integral exacta (3.13), con los factores y términos de datos, **como proposición objetivo sin prueba ni uso como axioma**. El paso pendiente construye una partición medible por vecinos más próximos, prueba `μr(A_{r,i})≤Cr εr²` y `μb(A_{b,j})≤Cb εb`, e integra la cota puntual. La frontera es un espacio de medida distinto del interior.

Para obtener (3.26) faltan la prueba de (3.13), la cobertura probabilística por ocupación de celdas i.i.d., y las estimaciones de escala `mr=O(mb²)` y `C_m a_m=O(mr^(−α/2))`. Para cobertura eventual casi segura se necesita un espacio de probabilidad común, eventos medibles de fallo, cotas sumables de sus probabilidades y Borel–Cantelli; la independencia se usa al calcular la probabilidad de que una celda quede vacía. La convergencia uniforme (3.27) requiere además pasar de pérdida poblacional pequeña a `C⁰` mediante Hölder y masas locales positivas. Las tasas (3.28) exigen cuantificar ese paso. Ninguna de estas conclusiones estadísticas se afirma como formalizada.

## Verificación

- Versiones fijadas: Lean 4.35.0, Mathlib v4.35.0, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- `lake build` local: éxito, 3200 trabajos. `#print axioms` en los teoremas nuevos: únicamente `propext`, `Classical.choice`, `Quot.sound`.
- Los módulos anteriores y el PDF no se modificaron. No se introdujeron `sorry`, `admit` ni axiomas nuevos.

