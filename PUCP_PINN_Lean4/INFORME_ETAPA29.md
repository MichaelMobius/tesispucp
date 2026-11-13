# Etapa 29 · Núcleo de la traza y Corolario 3.23

Base en la [PR #30](https://github.com/MichaelMobius/tesispucp/pull/30), commit `74f2140f7762a2c851aa2038629a37f7dccf9454`. La correspondencia se refiere al Corolario 3.23 de la página impresa 109 del PDF normativo.

## Núcleo de la traza

El dominio de `trazaSobolevCuadrado` es el subtipo `W12 volume cuadrado`. Un par ambiental `H1Graph` representa un elemento de $H^1$ cuando su segundo componente es el gradiente débil del primero. `H01` es la clausura en el grafo de las funciones de prueba. Las cuatro trazas usan Lebesgue unidimensional y sus igualdades son casi en todas partes en las caras abiertas.

1. `integral_partes_traza_cuadrado` expresa $\int_U(\partial_i\varphi\,v+\varphi D_iv)$ como la integral de cara positiva menos la de cara negativa. El interpolante afín en la coordenada normal se trata con el emparejamiento de la traza por adjuntos. Para el resto, el teorema del valor medio da una cota proporcional a la distancia a cada cara normal. Donde el recorte varía en la dirección normal, esa distancia es a lo sumo $2\delta$. El producto del resto con la derivada del recorte queda acotado de forma uniforme. La convergencia dominada permite aplicar al límite la identidad de derivada débil. El signo corresponde a las normales exteriores $+e_i$ y $-e_i$.
2. `extension_cero_traza_nula` aplica la identidad por coordenadas. Las dos trazas nulas eliminan los términos de frontera. Los indicadores de $U$ del valor y gradiente pertenecen a $L^2$ con Lebesgue bidimensional en el plano. El indicador del gradiente es el gradiente débil del indicador del valor.
3. Para $r_n=1+1/(n+1)$, la contracción evalúa la prolongación en $r_n x$ y multiplica su gradiente por $r_n$. El cambio de variables de Haar justifica la derivación débil y el control de la norma $L^2$. La continuidad de la dilatación se prueba primero para funciones continuas de soporte compacto, por convergencia dominada, y luego para todo $L^2$ por densidad y la cota uniforme del operador. El soporte contraído se encuentra en $[-1/r_n,1/r_n]^2\Subset U$.
4. `mem_H01_of_hasCompactSupport` de EllipticPDE aplica molificación con soporte interior a cada contracción. La convergencia de ambas componentes del grafo y la clausura de `H01` dan la inclusión inversa. `nucleo_trazaSobolevCuadrado_eq_H01` y `diferencia_mem_H01_de_trazas_iguales` establecen el núcleo y su consecuencia por linealidad.

`trazaSobolevCuadrado_continua` identifica cada componente con la restricción de un representante continuo en el cuadrado cerrado. Para una prueba tangencial suave se aplica la fórmula de frontera a su producto con un perfil normal apoyado, dentro del cuadrado, en una franja de ancho a lo sumo $2\delta$. La derivada del perfil es no positiva y tiene integral $-1$. Fubini y la continuidad uniforme muestran que la integral contra esa derivada recupera, con signo negativo, el valor de cara. El término que multiplica al gradiente débil converge a cero por convergencia dominada. La unicidad distribucional en el intervalo identifica las dos funciones casi en todas partes.

## Correspondencia con C3.23

| Ecuación | Declaración Lean | Hipótesis y conclusión |
|---|---|---|
| (3.80) | `poincare_cuadrado_espectral`, `poincare_cuadrado_constante_minima` | Constante óptima $\sqrt2/\pi$ en $H_0^1(U)$ y primer modo extremal. |
| (3.81)–(3.82) | `cotas_simultaneas323_traza` | Elementos arbitrarios de $H^1$ con igual traza y laplacianos distribucionales en $L^2$. El residuo es $\Delta h-f$. Las constantes son $\frac{\sqrt2}{\pi}\sqrt{1+2/\pi^2}$ y $0.26404$. La segunda norma es esencial. P3.22 aporta un representante continuo del error, nulo en la frontera. |
| (3.83) | `corolario323_traza` | Reutiliza los prefijos de la ley uniforme, las selecciones y comparadores de P3.15 en su instancia escalar con $\alpha=1/2$. El operador poblacional y su dato coinciden c.t.p. con los representantes de los laplacianos. La tasa conjunta es $O((\log m/m)^{1/4})$ casi seguramente y ambas normas tienden a cero. |

La medida uniforme del cuadrado tiene densidad $1/4$ respecto de Lebesgue restringida, por lo que `norma_residuo323_de_perdida_escalar` conserva $\|\Delta h-f\|_2=2\sqrt{E(h)}$. La tasa se deduce de P3.15 por `corolario323_escalar` y `transferencia_simultanea323`. Las hipótesis de selección mensurable y comparadores son las de `Selecciones315`. El resultado usa `∀ᵐ` y las mismas selecciones, sin exigir la mensurabilidad del mapa de los candidatos al grafo para esta implicación.

Queda como siguiente prioridad la arquitectura cuadrática común del Lema 3.24. Los comparadores y minimizadores de las instancias neuronales concretas siguen siendo obligaciones de los bloques posteriores.

## Verificación

Lean `4.35.0`, Mathlib `v4.35.0`, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. Los controles `#check` y `#print axioms` están en los módulos nuevos y ampliados. El SHA-256 del PDF normativo coincide con el inventario.
