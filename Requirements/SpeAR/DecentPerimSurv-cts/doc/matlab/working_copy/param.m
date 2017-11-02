% param.m
% r = r+1;

rand('state',2); % 2 is good for sine wave and step response

T = 3.5; % 14
N = 4;
v = 1; % normalized velocity for perimeter length of 1

% Note: to ensure no violation of turning constraints P/N/v >= 14*pi/3*R
% this means that a UAV can execute 2 consecutive turns (each of distance
% 7*pi/3*R) along any segment. This corresponds to the densest scenario.

p = track(N,v,T);

% r = inf*ones(length(p(:,1)), N);
% vel = p(1,(N+3):(2*N+2));
% t = p(1,1) - p(1,2:(N+1))/v;
% for k=2:length(p(:,1)),
%    for n=1:N,
%       if p(k,N+2+n) ~= vel(n),
%          r(k,n) = p(k,1) - t(n);
%          vel(n) = p(k,N+2+n);
%          t(n) = p(k,1);
%       else,
%          r(k,n) = r(k-1,n);
%       end;
%    end;
% end;
% figure(3); clf;
% plot(p(:,1),r);
% min(min(r))

plot_animation(p,N,T);