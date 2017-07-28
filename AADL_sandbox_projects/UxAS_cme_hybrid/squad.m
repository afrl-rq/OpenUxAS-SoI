%% Summer of Innovation, Hybrid Systems Group
%  Wright Brothers Institute
%  Air Force Research Laboratory
%  Lockheed Martin Aeronautics
%  Chris Elliott, July 2017

clear all; close all;

% adjacency
%A = ones(5,5) - eye(5); % complete

% A = [0 1 1 0 0 0; 
%      0 0 1 1 0 0; 
%      1 0 0 0 1 0; 
%      0 0 0 0 0 1;
%      0 0 0 0 0 1;
%      0 1 0 0 0 0]' ; %take transpose since we input Columns as Rows

% A = [0 1 0 0 0 0 0 0;
%      0 0 1 0 0 0 0 0;
%      1 0 0 0 0 0 0 0;
%      0 0 0 0 0 0 0 1;
%      0 0 0 1 0 0 0 0;
%      0 0 0 0 0 1 0 0;
%      0 0 0 0 0 0 0 0;
%      0 0 0 0 0 0 0 0]

% gossip ring
nagents = 64; 

   idx = [2:1:nagents, 1]
  A = zeros(nagents,nagents);
  for ii = 1:nagents
for jj = 1:nagents
temp = zeros(1,nagents);
temp(1,idx(ii)) = 1;
A(ii,:) =  temp;
end
end
%  A = randi([0 1],20,20)
A = A';
 
 
 nagents = length(A);
 
 G = digraph(A);
 %L = laplacian(G)
 
 % find the Laplacian and Diagonal In-Degree Matrix
 [L, D] = lapl(A)

  P = zeros(length(L));
  P(5,5) = 1;%eye(100);

  
 %% Simulation
 clear t x consens
 
 %ic = 100*rand(length(L),1); % random the initial conditions, and repeat for all graphs
 
 % instead of random ic's, just set the leader value
 ic = 100*ones(length(L),1);
 ic(1,1) = 10;
 x0 = ic(1,1);
 [t,x] = ode23(@(t,x) cooptrack(t,x,L,P,1,x0),[0 250],ic);
 
 fs = 14;
 figure(1)
 subplot(121), plot(G,'markersize',9,'arrowsize',12,'edgecolor','k'); grid; xlabel('E [nm]'); ylabel('N [nm]');
  title('UxAS Connectivity')
  set(gca,'fontsize',fs)
 subplot(122), plot(t,x,t,ic(1,1)*ones(length(t),1),'r--','linewidth',1.4); ylabel('Cost'); xlabel('t [sec]'); grid; ylim([0 100]);
  title('RouteAggregatorService')
  set(gca,'fontsize',fs)