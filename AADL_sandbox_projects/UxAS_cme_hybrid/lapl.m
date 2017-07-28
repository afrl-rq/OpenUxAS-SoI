function [L, D] = lapl(A)
%function [L, D] = lapl(A)
% given Adjacency Matrix A
% compute the Laplacian Matrix L
% and the Diagonal In-Degree Matrix D
% EE 5329, Dr. Lewis
% Chris Elliott 1/27/2013

n = length(A);
L = zeros(n);
D = zeros(n);

for ii = 1:n
    D(ii,ii) = sum(A(ii,:));
end

L = D - A;

if sum(L')*ones(n,1) ~= 0
    error('Invalid Laplacian')
end

end

