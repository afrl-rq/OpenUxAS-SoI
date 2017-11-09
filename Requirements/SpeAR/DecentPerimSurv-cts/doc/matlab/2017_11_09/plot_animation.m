function plot_animation(p,N,T)

Ts = 0.01;

figure(2); clf;
plot(p(:,1),p(:,N+2),'k','LineWidth',2); hold on;
plot(p(:,1),zeros(size(p(:,1))),'k','LineWidth',2);
for n=1:N,
    %plot(p(:,1)+(n-1)*(1e-2)*ones(size(p(:,1))),p(:,(n+1)),'LineWidth',2);
    plot(p(:,1),p(:,(n+1)),'LineWidth',2);
    plot(p(:,1),n/N*ones(size(p(:,1))),'k--','LineWidth',1);
end;

% % plot intervals of V/P
% plot([1 1], [0 1],'k','LineWidth',2);
% plot([2 2], [0 1],'k','LineWidth',2);

% title('Position');
v = axis;
v(1) = 0;
v(2) = T;
v(3) = v(3) - 0.001;
v(4) = v(4) + 0.003;
axis(v)
% grid on
% axis off

ylab = get(gca,'YTickLabel');
[total, width] = size(ylab);

if width < 2,
   for n=1:total,
      nylab(n,:) = [ylab(n) ' '];
   end;
   ylab = nylab;
end;

for n=1:total,
   for ti=1:floor(max(p(:,N+2))),
      if strcmp(ylab(n,:),[num2str(ti) ' ']) == 1,
         if ti == 1,
            ylab(n,:) = 'P ';
         else
            ylab(n,:) = [num2str(ti) 'P'];
         end;
      end;
      if strcmp(ylab(n,:),[num2str(ti) '  ']) == 1,
         if ti == 1,
            ylab(n,:) = 'P  ';
         else
            ylab(n,:) = [num2str(ti) 'P '];
         end;
      end;
   end;
end;
set(gca,'YTickLabel',ylab);

xlab = get(gca,'XTickLabel');
[total, width] = size(xlab);

if width < 2,
   for n=1:total,
      nxlab(n,:) = [xlab(n) ' '];
   end;
   xlab = nxlab;
end;

for n=1:total,
   for ti=1:floor(p(end,1)),
      if strcmp(xlab(n,:),[num2str(ti) ' ']) == 1,
         xlab(n,:) = [num2str(ti) 'T'];
      end;
      if strcmp(xlab(n,:),[num2str(ti) '  ']) == 1,
         xlab(n,:) = [num2str(ti) 'T '];
      end;
   end;
end;
set(gca,'XTickLabel',xlab);

set(gca,'FontSize',20)

return;

t = [];
for k=1:length(p(:,1))-1,
   t = [t, p(k,1):Ts/2:p(k+1,1)];
end;
t = t';
uav = zeros(length(t),N);
for n=1:N,
   uav(:,n) = interp1q(p(:,1), p(:,n+1), t);
end;
P = interp1q(p(:,1), p(:,N+2), t);

pause_scene = 0;
figure(1); clf;
set(gcf,'DoubleBuffer','on');
set(gcf,'WindowStyle','modal');
pA = plot([0 P(1)], [0 0], 'k'); hold on;
plot([0 0], [0.05 -0.05],'k');
pB = plot([P(1) P(1)], [0.05 -0.05],'k');
A = [];
B = [];
for n=1:N,
   if mod(n,2) == 0,
      A = [A; text( uav(1,n), 0.1, num2str(n),'HorizontalAlignment','center','FontWeight','bold')];
   else
      A = [A; text( uav(1,n), -0.1, num2str(n),'HorizontalAlignment','center','FontWeight','bold')];
   end;
   
   B = [B; plot( uav(1,n), 0, '.' )];
end;
T = text(0.5,-0.2,['t = ' num2str(round(t(1)*100)/100)],'HorizontalAlignment','center');
DText = text(0.5,-0.5,' ','HorizontalAlignment','center');
axis([-0.5, max(P) + 0.5, -0.5, 0.5]);
axis equal;
axis off;
 
%return;

time = t(1);
set(gcf,'CurrentCharacter', char(0));
k = 1;
K = 1;

f = 3;

% aviobj = avifile('fixed_coord.avi','FPS',30);
% aviobj.Quality = 100;
while time <= t(end),

   switch get(gcf,'CurrentCharacter'),
      case 'c',
         set(gcf,'CurrentCharacter', char(0));
         figure(1);
      case 'd',
         figure(f); clf;
         f = f + 1;
         plot(get(pA,'Xdata'),get(pA,'Ydata'),'k'); hold on;
         plot([0 0], [0.05 -0.05],'k');
         plot(get(pB,'Xdata'),get(pB,'Ydata'),'k');
         
         px = get(pB,'Xdata');
         for n=1:(N-1),
            plot(px(1)*[n/N n/N], [0.02 -0.02],'k');
         end;
         
         for n=1:N,
            pos = get(A(n),'Position');
            text(pos(1),pos(2),get(A(n),'String'),'HorizontalAlignment','center','FontWeight','bold');
            plot(get(B(n),'Xdata'),get(B(n),'Ydata'),'b.');
         end;
         axis([-0.5, max(P) + 0.5, -0.5, 0.5]);
         axis equal;
         axis off;
         set(1,'CurrentCharacter', char(0));
         pause_scene = 1;
      case 'p',
         pause_scene = 1 - pause_scene;
         set(gcf,'CurrentCharacter', char(0));
         figure(1);
      case 'r',
         set(gcf,'CurrentCharacter', char(0));
         time = t(1);
         figure(1);
      case 'q',
%          aviobj = close(aviobj);
         return;
      case 'x',
%          aviobj = close(aviobj);
         close 1;
         return;
   end;
    
   if pause_scene == 0,
      kk = find(t(k:end) <= time);
      k = kk(end) + k - 1;
      set(pA, 'Xdata', [0, P(k)]);
      set(pB, 'Xdata', [P(k), P(k)]);
      for n=1:N,
         if mod(n,2) == 0,
            set(A(n), 'Position', [ uav(k,n), 0.1]);
         else
            set(A(n), 'Position', [ uav(k,n), -0.1]);
         end;
         
         set(B(n), 'Xdata', uav(k,n));
      end;
      set(T,'String',['t = ' sprintf('%.2f',round(t(k)*100)/100)]);
      set(T,'Position',[P(k)/2, -0.2]);
      set(DText,'Position',[P(k)/2, -0.5]);
      time = time + Ts;

%       if t(k) >= p(K,1),
%          pause_scene = 1;
%          set(pA, 'Xdata', [0, p(K,N+2)]);
%          set(pB, 'Xdata', [p(K,N+2), p(K,N+2)]);
%          for n=1:N,
%             if mod(n,2) == 0,
%                set(A(n), 'Position', [ p(K,n+1), 0.1]);
%             else,
%                set(A(n), 'Position', [ p(K,n+1), -0.1]);
%             end;
% 
%             set(B(n), 'Xdata', p(K,n+1));
%          end;
%          set(T,'String',['t = ' sprintf('%.2f',round(p(K,1)*100)/100)]);
%          set(T,'Position',[p(K,N+2)/2, -0.2]);
%          set(DText,'Position',[p(K,N+2)/2, -0.5]);
%       
%          set(DText,'String', num2str(find(p(K,(2*N+3):end) == 1)) );
%          K = K+1;
%       end;

      drawnow
%       aviobj = addframe(aviobj,getframe(gcf));
      pause(0.01);

   else
      drawnow
      pause(0.1);
   end;
   
end;

set(pA, 'Xdata', [0, P(end)]);
set(pB, 'Xdata', [P(end), P(end)]);
for n=1:N,
   if mod(n,2) == 0,
      set(A(n), 'Position', [ uav(end,n), 0.1]);
   else
      set(A(n), 'Position', [ uav(end,n), -0.1]);
   end;

   set(B(n), 'Xdata', uav(end,n));
end;
set(T,'String',['t = ' sprintf('%.2f',round(t(end)*100)/100)]);
set(T,'Position',[P(end)/2, -0.2]);
% aviobj = addframe(aviobj,getframe(gcf));
% aviobj = close(aviobj);

