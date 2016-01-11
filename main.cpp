#include <memory>
#include <utility>
#include <string>
#include <experimental/optional>

#include <cstdio>
#include <cassert>

namespace {
/// An abstract class that represents a mathematical expression
class Expr {
 public:
  virtual ~Expr() {}

  /// Returns the result of f(x), where f(x) = Expr
  virtual float eval_at(float) const = 0;
};

class NumExpr final : public Expr {
 public:
  const float x_;

  NumExpr(float x) : x_((x)) {}
  ~NumExpr() {}

  virtual float eval_at(float) const { return x_; }
};

/// All user defined variables will be represented by this expression
class VarExpr final : public Expr {
 public:
  const std::string name_;
  const std::shared_ptr<Expr> expr_;

  VarExpr(const std::string name)
      : name_(name), expr_(std::make_shared<NumExpr>(1)) {}
  VarExpr(const std::string name, const std::shared_ptr<Expr> expr)
      : name_(name), expr_(std::move(expr)) {}
  ~VarExpr() {}

  bool operator==(const VarExpr& other) { return name_ == other.name_; }

  /* FIXME: eval should only work for the specified variable */
  virtual float eval_at(float x) const { return expr_->eval_at(x); }
};

/// Represents the sum of two expresions
class SumExpr final : public Expr {
 public:
  const std::shared_ptr<Expr> addend_;
  const std::shared_ptr<Expr> augend_;

  SumExpr(const std::shared_ptr<Expr>& addend,
          const std::shared_ptr<Expr>& augend)
      : addend_(std::move(addend)), augend_(std::move(augend)) {}
  ~SumExpr() {}

  virtual float eval_at(const float x) const {
    return addend_->eval_at(x) + augend_->eval_at(x);
  }
};

class ProdExpr final : public Expr {
 public:
  const std::shared_ptr<Expr> multiplier_;
  const std::shared_ptr<Expr> multiplicand_;

  ProdExpr(const std::shared_ptr<Expr>& multiplier,
           const std::shared_ptr<Expr>& multiplicand)
      : multiplier_(std::move(multiplier)),
        multiplicand_(std::move(multiplicand)) {}
  ~ProdExpr() {}

  virtual float eval_at(float x) const {
    return multiplier_->eval_at(x) * multiplicand_->eval_at(x);
  }
};

/// Checks the expression type
template <typename ExprType>
static inline bool expr_type_is(const std::shared_ptr<Expr>& unknown_expr) {
  const auto checked_expr_type =
      std::dynamic_pointer_cast<ExprType>(unknown_expr);
  return checked_expr_type != nullptr;
}

/// derive calculates the derivative of the given expresion
///
/// \param expr The expresion to be evaluated and reduced
/// \param var The variable the function is evaluating with respect to
/// \return An expression that is result of applying f'(f(x))
static std::shared_ptr<Expr> derive(const std::shared_ptr<Expr>& expr,
                                    const std::shared_ptr<VarExpr> var) {
  // NOTE: there is no need to copy the entire tree expression when casting
  // Check the supplied expression and evaluate the derivative
  if (expr_type_is<NumExpr>(expr)) {
    // if f(x) = n , where n in N, then f'(x) = 0
    return std::make_shared<NumExpr>(0);
  } else if (expr_type_is<VarExpr>(expr)) {
    // if f(x) = x then f'(x) = 1
    const auto var_expr = std::dynamic_pointer_cast<VarExpr>(expr);
    if (var_expr.get() == var.get()) return std::make_shared<NumExpr>(1);
    return std::make_shared<NumExpr>(0);
  } else if (expr_type_is<SumExpr>(expr)) {
    // if f(x) = g(x) + h(x) then f'(x) = g'(x) + h'(x)
    const auto sum_expr = std::dynamic_pointer_cast<SumExpr>(expr);
    const auto addend_x = derive(sum_expr->addend_, var);
    const auto augend_x = derive(sum_expr->augend_, var);
    // TODO: This must be reduced
    return std::make_shared<SumExpr>(addend_x, augend_x);
  } else if (expr_type_is<ProdExpr>(expr)) {
    // if f(x) = g(x) * h(x) then f'(x) = g'(x) * h(x) + h'(x) * g(x)
    const auto prod_expr = std::dynamic_pointer_cast<ProdExpr>(expr);

    static const auto derive_prod = [&var](const std::shared_ptr<Expr>& x1,
                                           const std::shared_ptr<Expr>& x2) {
      const auto addend = derive(x1, var);
      return std::make_shared<ProdExpr>(addend, x2);
    };

    const auto prod_expr_addend =
        derive_prod(prod_expr->multiplier_, prod_expr->multiplicand_);
    const auto prod_expr_augend =
        derive_prod(prod_expr->multiplicand_, prod_expr->multiplier_);
    return std::make_shared<SumExpr>(prod_expr_addend, prod_expr_augend);
  }
  return nullptr;
}

}  // namespace

int main() {
  /* NumExpr */
  const auto f1 = std::make_shared<NumExpr>(100);  // f(x) = 100
  const auto ans = derive(f1, nullptr)->eval_at(20);
  assert(ans == 0);  // f(x) = 0

  /* VarExpr */
  const auto x = std::make_shared<VarExpr>("x");
  const auto x0 = std::make_shared<VarExpr>("x");
  const auto y = std::make_shared<VarExpr>("y");

  const auto ans0 = derive(x, x)->eval_at(0);
  assert(ans0 == 1);  // f(x) = 1
  const auto ans1 = derive(x, y)->eval_at(0);
  assert(ans1 == 0);  // f(y) = 0

  /* SumExpr */
  const auto sumx = std::make_shared<SumExpr>(f1, x);  // f(x) = 100 + x
  const auto sumy = std::make_shared<SumExpr>(x, x);   // f(y) = 2x

  const auto ans2 = derive(sumx, x)->eval_at(0);
  assert(ans2 == 1);  // f(x) = 1
  const auto ans3 = derive(sumy, y)->eval_at(0);
  assert(ans3 == 0);  // f(y) = 0

  /* ProdExpr */
  const auto prodx =
      std::make_shared<ProdExpr>(std::make_shared<NumExpr>(1), x);  // f(x) = x
  const auto prodx0 = std::make_shared<ProdExpr>(y, x);             // f(x) = xy
  const auto prodx1 = std::make_shared<ProdExpr>(x, x);  // f(x) = x^2
  const auto prodx2 =
      std::make_shared<ProdExpr>(sumx, prodx1);  // f(x) = 100x^2 + x^3

  const auto ans4 = derive(prodx, x)->eval_at(0);
  assert(ans4 == 1);                                // f(x) = 1
  const auto ans5 = derive(prodx0, y)->eval_at(0);  // f(y) = x
  /* NOTE: variables are set to one, so f(0) = x = 0 for now, this test is also
   * muli variable */
  assert(ans5 == 1);
  const auto ans6 = derive(prodx1, x)->eval_at(1);  // f(x) = 2x
  assert(ans6 == 2);
  const auto ans7 = derive(prodx2, x)->eval_at(1);  // f(x) = 200x + 3x^2
  /* FIXME: Although its numerically correct, the program does not yet evaluate
   * variables with exponents */
  assert(ans7 == 3);
}
