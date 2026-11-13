# Etapa 26 · Completitud de los senos de Dirichlet

Base: [PR #27](https://github.com/MichaelMobius/tesispucp/pull/27), commit `9dd6893ec09938af52346828790e65ced3e852d8`. Fuente normativa: páginas impresas 105–109 del PDF identificado por hash en el inventario.

## Completitud

Se usa Stone–Weierstrass en el intervalo cerrado y en el cuadrado cerrado. El coseno de primera frecuencia es estrictamente decreciente en la coordenada reescalada a $[0,\pi]$. En el cuadrado los cosenos de las dos coordenadas separan puntos. La recurrencia $2\cos(t)\sin(nt)=\sin((n+1)t)+\sin((n-1)t)$ implica que multiplicar por cada coseno preserva el subespacio de combinaciones finitas. En particular, los productos del primer modo con polinomios en los cosenos están en ese subespacio. Su álgebra de multiplicadores separa puntos y es uniformemente densa. Esta ruta usa la aproximación real sobre compactos de Mathlib. La ruta de Fourier habría requerido además construir la extensión impar y convertir entre Lebesgue y Haar normalizada del círculo.

Si una función continua tiene soporte compacto dentro del abierto, el cociente por el primer modo es continuo: en el interior el modo es positivo y en un entorno del complemento del dominio la función es localmente cero. Al multiplicar la aproximación uniforme del cociente por el primer modo se obtienen aproximaciones de esa función. Se registra también la densidad de continuas de soporte compacto en los subtipos abiertos con las medidas inducidas.

Para el paso a todas las clases de $L^2$, la prueba principal usa el complemento ortogonal. La inclusión del compacto induce una isometría desde el $L^2$ ambiental al $L^2$ del subtipo con la medida inducida. Si $z$ es ortogonal a los modos, también es ortogonal a $w g$ para toda función continua $g$ en el compacto, donde $w$ es el primer modo. Así $wz$ es ortogonal a todas las continuas. La densidad de estas en $L^2$ implica $wz=0$. La positividad de $w$ casi en todas partes implica $z=0$. Esta prueba aplica tanto al intervalo como al cuadrado y evita una construcción adicional de productos tensoriales de espacios de Hilbert.

## Correspondencia con la Proposición 3.22

| Paso | Declaración Lean |
|---|---|
| Completitud en el intervalo y en el cuadrado | `senoDirichletLp_complete`, `modoSenoLp_complete` |
| Unicidad por coeficientes en todo $L^2(U)$ | `modoSenoLp_eq_zero_of_inner_eq_zero` |
| Base de Hilbert de los modos | `baseHilbertSenoCuadrado` |
| Expansión de cualquier elemento y Parseval (3.78) | `modoSenoLp_expansion`, `modoSenoLp_parseval` |
| La serie representa la clase del error | `serieSeno_representa_error` |
| Representante continuo y estimación (3.77) | `proposicion322_espectral_completa` |

La etapa 25 proporciona una clase $w\in L^2$ que representa la suma continua y conserva los coeficientes de $e$. La etapa 26 aplica la completitud a $e-w$ para obtener la igualdad en $L^2$. El teorema principal cuantifica sobre $e\in H_0^1(U)$ y un representante $r\in L^2(U)$ de $\Delta e$. La igualdad débil heredada utiliza $F=-r$, como en (3.79). La medida es Lebesgue restringida y los índices Lean $0,1,\dots$ corresponden a las frecuencias físicas $1,2,\dots$.

El representante es continuo en todo el plano y nulo en la frontera. El teorema identifica el supremo en la clausura con la norma esencial del error y prueba para ambos las cotas $C_{\mathrm{esp}}\|r\|_2$ y $0.26404\|r\|_2$. Se reutilizan la convergencia uniforme y el certificado de la etapa 25.

## Corolario 3.23

`poincare_cuadrado_espectral` demuestra (3.80) para todo $H_0^1$. Green da la ortonormalidad de los gradientes de los modos divididos por $\sqrt{\lambda_{jk}}$. Bessel para esos gradientes, el mínimo $\lambda_{11}=\pi^2/2$ y Parseval para el error dan la desigualdad con $\sqrt 2/\pi$. La prueba usa únicamente la completitud en $L^2$. `poincare_cuadrado_primer_modo` da igualdad y `poincare_cuadrado_constante_minima` prueba optimalidad.

`energia_cuadrado_poincare_optima` aplica el núcleo energético del Lema 3.19 y verifica la constante de (3.81) para un error dado en $H_0^1$. La cota (3.82) se obtiene de P3.22 para el mismo error. Para la versión completa de C3.23 quedan la identificación de igual traza con diferencia en $H_0^1$ y la aplicación simultánea a la tasa de P3.15 en (3.83).

## Reproducción

Ejecutar `lake build` con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. Las declaraciones principales tienen comprobaciones `#check` y `#print axioms` en los módulos de completitud, P3.22 y Poincaré.

La compilación local completó 3296 trabajos. La auditoría de las nuevas declaraciones principales devuelve `propext`, `Classical.choice` y `Quot.sound`.
